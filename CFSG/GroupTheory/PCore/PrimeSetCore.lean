module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSetCore

public section

namespace CFSG

open SignalizerFunctor
open scoped Pointwise

@[expose]
def primeSupported (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

@[expose]
def primeSetCore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ primeSupported π (Nat.card N)}

instance primeSetCore_normal (π : Set ℕ) (G : Type*) [Group G] :
    (primeSetCore π G).Normal :=
  Subgroup.normal_sSup _ (fun _ h => h.1)

theorem primeSetCore_eq_helpersPrimeSetCore (π : Set ℕ) (G : Type*) [Group G] :
    primeSetCore π G = Helpers.primeSetCore (GroupType := G) π := by
  rw [primeSetCore, sSup_eq_iSup', iSup_subtype]
  rfl

theorem primeSupported_singleton_iff_isPGroup {H : Type*} [Group H] [Finite H] (p : ℕ)
    (hp : p.Prime) : primeSupported {p} (Nat.card H) ↔ IsPGroup p H := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hs
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun hq hd => hs _ hq hd)
  · intro h q hq hd
    obtain ⟨n, hn⟩ := h.exists_card_eq
    exact Nat.prime_eq_prime_of_dvd_pow hq hp (hn ▸ hd)

theorem primeSupported_compl_singleton_iff_coprime {H : Type*} [Group H] [Finite H] (p : ℕ)
    (hp : p.Prime) : primeSupported {p}ᶜ (Nat.card H) ↔ Nat.Coprime p (Nat.card H) := by
  rw [hp.coprime_iff_not_dvd]
  exact ⟨fun hs hd => Set.mem_compl_singleton_iff.mp (hs p hp hd) rfl,
    fun hd q _ hqd => Set.mem_compl_singleton_iff.mpr fun hq => hd (hq ▸ hqd)⟩

theorem primeSetCore_singleton_eq_pCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) : primeSetCore {p} G = pCore p G := by
  unfold primeSetCore pCore
  congr 1
  ext N
  exact and_congr_right fun _ => primeSupported_singleton_iff_isPGroup p hp

theorem primeSetCore_compl_singleton_eq_pPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) : primeSetCore {p}ᶜ G = pPrimeCore p G := by
  unfold primeSetCore pPrimeCore
  congr 1
  ext N
  exact and_congr_right fun _ => primeSupported_compl_singleton_iff_coprime p hp

theorem pCore_eq_helpersPrimeSetCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) : pCore p G = Helpers.primeSetCore (GroupType := G) {p} := by
  rw [← primeSetCore_singleton_eq_pCore hp, primeSetCore_eq_helpersPrimeSetCore]

theorem pPrimeCore_eq_helpersPrimeSetCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) : pPrimeCore p G = Helpers.primeSetCore (GroupType := G) {p}ᶜ := by
  rw [← primeSetCore_compl_singleton_eq_pPrimeCore hp, primeSetCore_eq_helpersPrimeSetCore]

theorem primeSetCore_maximal {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    primeSupported π (Nat.card (primeSetCore π G)) ∧
      ∀ N : Subgroup G, N.Normal → primeSupported π (Nat.card N) →
        N ≤ primeSetCore π G := by
  refine ⟨?_, fun N hN hsupp => le_sSup ⟨hN, hsupp⟩⟩
  rw [primeSetCore_eq_helpersPrimeSetCore]
  exact Helpers.prime_set_core_supported π

private theorem primeSetCore_map_le {G H : Type*} [Group G] [Group H] (π : Set ℕ)
    (f : G ≃* H) :
    (primeSetCore π G).map f.toMonoidHom ≤ primeSetCore π H := by
  rw [primeSetCore, sSup_eq_iSup, Subgroup.map_iSup]
  refine iSup_le fun N => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hN => le_sSup ⟨hN.1.map f.toMonoidHom f.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective f.injective]
  exact hN.2

theorem primeSetCore_map_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (π : Set ℕ) (f : G ≃* H) :
    (primeSetCore π G).map f.toMonoidHom = primeSetCore π H := by
  refine le_antisymm (primeSetCore_map_le π f) ?_
  have h := Subgroup.map_mono (f := f.toMonoidHom) (primeSetCore_map_le π f.symm)
  have hid : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id H := by ext; simp
  rwa [Subgroup.map_map, hid, Subgroup.map_id] at h

theorem primeSetCore_characteristic_and_normal {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    (primeSetCore π G).Characteristic ∧ (primeSetCore π G).Normal :=
  ⟨Subgroup.characteristic_iff_map_eq.mpr fun f => primeSetCore_map_mulEquiv π f,
    inferInstance⟩

theorem primeSetCore_quotient_primeSetCore_eq_bot {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    primeSetCore π (G ⧸ primeSetCore π G) = ⊥ := by
  have key : ∀ (K : Subgroup G) [K.Normal],
      K = Helpers.primeSetCore (GroupType := G) π →
        primeSetCore π (G ⧸ K) = ⊥ := by
    intro K _ hK
    subst hK
    rw [primeSetCore_eq_helpersPrimeSetCore]
    exact Helpers.prime_set_core_quotient_trivial π
  exact key _ (primeSetCore_eq_helpersPrimeSetCore π G)

theorem pPrimeCore_quotient_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ := by
  have key : ∀ (K : Subgroup G) [K.Normal], K = primeSetCore {p}ᶜ G →
      pPrimeCore p (G ⧸ K) = ⊥ := by
    intro K _ hK
    subst hK
    rw [← primeSetCore_compl_singleton_eq_pPrimeCore hp]
    exact primeSetCore_quotient_primeSetCore_eq_bot _
  exact key _ (primeSetCore_compl_singleton_eq_pPrimeCore hp).symm

private theorem index_dvd_card_of_sup_eq_top {G : Type*} [Group G] [Finite G]
    (N V : Subgroup G) [N.Normal] (hNV : N ⊔ V = ⊤) : V.index ∣ Nat.card N := by
  let f := (QuotientGroup.mk' N).domRestrict V
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ N ⊔ V := by rw [hNV]; trivial
    obtain ⟨n, hn, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨v, hv⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    change QuotientGroup.mk' N v = QuotientGroup.mk' N (n * v)
    rw [map_mul, hn1, one_mul]
  have hker := Subgroup.card_ker_mul_card_of_surjective hf
  have hN := N.card_mul_index
  rw [Subgroup.index_eq_card] at hN
  have hcard : Nat.card f.ker * V.index * Nat.card (G ⧸ N) =
      Nat.card N * Nat.card (G ⧸ N) := by
    calc Nat.card f.ker * V.index * Nat.card (G ⧸ N)
        = (Nat.card f.ker * Nat.card (G ⧸ N)) * V.index := by ring
      _ = Nat.card V * V.index := by rw [hker]
      _ = Nat.card G := V.card_mul_index
      _ = Nat.card N * Nat.card (G ⧸ N) := hN.symm
  exact ⟨Nat.card f.ker, by
    rw [mul_comm]; exact (Nat.mul_right_cancel (Nat.card_pos (α := G ⧸ N)) hcard).symm⟩

private theorem le_of_isPGroup_of_coprime_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (N V : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) (hV : Nat.Coprime p V.index) : N ≤ V := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p V := Classical.choice inferInstance
  obtain ⟨S, hS⟩ := P.exists_comap_subtype_eq
  let P' := (P : Subgroup V).map V.subtype
  have hP'S : P' ≤ (S : Subgroup G) := by
    change (P : Subgroup V).map V.subtype ≤ _
    rw [← hS, Subgroup.map_comap_eq]
    exact inf_le_right
  have hfact : (Nat.card V).factorization p = (Nat.card G).factorization p := by
    conv_rhs => rw [← V.card_mul_index]
    rw [Nat.factorization_mul Nat.card_pos.ne'
      (by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne')]
    simp only [Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hV), add_zero]
  have hcard : Nat.card P' = Nat.card (S : Subgroup G) := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, P.card_eq_multiplicity,
      S.card_eq_multiplicity, hfact]
  have hP'eq := Subgroup.eq_of_le_of_card_ge hP'S hcard.ge
  exact (hN.le_sylow_of_normal S).trans (by rw [← hP'eq]; exact Subgroup.map_subtype_le _)

theorem pCore_le_of_coprime_normal_mul_eq_univ {U : Type*} [Group U] [Finite U]
    (p : ℕ) (hp : p.Prime) (R V : Subgroup U) [R.Normal]
    (hR : Nat.Coprime p (Nat.card R))
    (hprod : (R : Set U) * (V : Set U) = Set.univ) :
    (∀ W : Subgroup U, W.Normal → IsPGroup p W → W ≤ V) ∧
      pCore p U ≤ V := by
  have hRV : R ⊔ V = ⊤ := SetLike.coe_injective <| by
    simpa only [Subgroup.coe_top] using (Subgroup.normal_mul R V).trans hprod
  have hV := hR.of_dvd_right (index_dvd_card_of_sup_eq_top R V hRV)
  have hle : ∀ W : Subgroup U, W.Normal → IsPGroup p W → W ≤ V :=
    fun W _ hW => le_of_isPGroup_of_coprime_index hp W V hW hV
  exact ⟨hle, hle _ inferInstance pCore_isPGroup⟩

section Conjugate

variable {G : Type*} [Group G]

theorem mem_conjugate_iff (Z : Subgroup G) (c y : G) :
    y ∈ conjugate Z c ↔ c * y * c⁻¹ ∈ Z := by
  rw [conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hh
    refine ⟨c * y * c⁻¹, hh, ?_⟩
    simp [mul_assoc]

@[simp]
theorem conjugate_one (Z : Subgroup G) : conjugate Z 1 = Z := by
  ext x
  simp [mem_conjugate_iff]

theorem conjugate_conjugate (Z : Subgroup G) (a b : G) :
    conjugate (conjugate Z a) b = conjugate Z (a * b) := by
  ext x
  simp only [mem_conjugate_iff, mul_inv_rev, mul_assoc]

theorem conjugate_eq_self_of_mem_normalizer {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) : conjugate Z g = Z := by
  ext x
  rw [mem_conjugate_iff]
  exact (Subgroup.mem_normalizer_iff.mp hg x).symm

theorem map_conjugate {G' : Type*} [Group G'] (f : G →* G') (Z : Subgroup G) (g : G) :
    (conjugate Z g).map f = conjugate (Z.map f) (f g) := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]

theorem map_conj_conjugate (Z : Subgroup G) (a b : G) :
    (conjugate Z a).map (MulAut.conj b).toMonoidHom = conjugate Z (a * b⁻¹) := by
  rw [conjugate, conjugate, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Conjugate

end CFSG

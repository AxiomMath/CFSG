module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Block
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfTables
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.OmGen

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

section Actions

variable {H Ω : Type*} [Group H] [MulAction H Ω]

private theorem card_stabilizer_mul_ncard_orbit [Finite H] (ω : Ω) :
    Nat.card (MulAction.stabilizer H ω) * (MulAction.orbit H ω).ncard = Nat.card H := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]

private theorem orbit_subgroup_subset (ω : Ω) (K : Subgroup H) :
    MulAction.orbit K ω ⊆ MulAction.orbit H ω := by
  rintro _ ⟨k, rfl⟩
  exact MulAction.mem_orbit ω (k : H)

theorem stab_eq_of_card [Finite H] (ω : Ω) (C K : Subgroup H)
    (hC : C ≤ MulAction.stabilizer H ω) {c o : ℕ} (hc : c ≤ Nat.card C)
    (ho : o ≤ (MulAction.orbit K ω).ncard) (hco : Nat.card H ≤ c * o) :
    C = MulAction.stabilizer H ω ∧ MulAction.orbit K ω = MulAction.orbit H ω ∧
      Nat.card C = c ∧ (MulAction.orbit H ω).ncard = o := by
  have hfin : (MulAction.orbit H ω).Finite := Set.finite_range _
  have h1 : Nat.card C ≤ Nat.card (MulAction.stabilizer H ω) := Subgroup.card_le_of_le hC
  have h2 : (MulAction.orbit K ω).ncard ≤ (MulAction.orbit H ω).ncard :=
    Set.ncard_le_ncard (orbit_subgroup_subset ω K) hfin
  have h3 := card_stabilizer_mul_ncard_orbit (H := H) ω
  have hs : 0 < Nat.card (MulAction.stabilizer H ω) := Nat.card_pos
  have hn : 0 < (MulAction.orbit H ω).ncard := by
    have hH : 0 < Nat.card H := Nat.card_pos
    rcases Nat.eq_zero_or_pos (MulAction.orbit H ω).ncard with h0 | h0
    · rw [h0, mul_zero] at h3
      omega
    · exact h0
  have hcs : c = Nat.card (MulAction.stabilizer H ω) := by
    have : Nat.card (MulAction.stabilizer H ω) ≤ c := by
      refine Nat.le_of_mul_le_mul_right (c := (MulAction.orbit H ω).ncard) ?_ hn
      calc Nat.card (MulAction.stabilizer H ω) * (MulAction.orbit H ω).ncard = Nat.card H := h3
        _ ≤ c * o := hco
        _ ≤ c * (MulAction.orbit H ω).ncard := Nat.mul_le_mul_left c (ho.trans h2)
    omega
  have hos : (MulAction.orbit H ω).ncard ≤ o := by
    refine Nat.le_of_mul_le_mul_left (c := Nat.card (MulAction.stabilizer H ω)) ?_ hs
    calc Nat.card (MulAction.stabilizer H ω) * (MulAction.orbit H ω).ncard = Nat.card H := h3
      _ ≤ c * o := hco
      _ = Nat.card (MulAction.stabilizer H ω) * o := by rw [hcs]
  have hoe : (MulAction.orbit H ω).ncard = o := by omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hC (by omega), ?_, by omega, hoe⟩
  exact Set.eq_of_subset_of_ncard_le (orbit_subgroup_subset ω K) (by omega) hfin

theorem orbit_eq_of_ncard_le [Finite H] (ω : Ω) (K : Subgroup H)
    (h : (MulAction.orbit H ω).ncard ≤ (MulAction.orbit K ω).ncard) :
    MulAction.orbit K ω = MulAction.orbit H ω :=
  Set.eq_of_subset_of_ncard_le (orbit_subgroup_subset ω K) h (Set.finite_range _)

theorem eq_top_of_orbit_eq (ω : Ω) {K M : Subgroup H} (hK : K ≤ M)
    (hstab : MulAction.stabilizer H ω ≤ M)
    (horb : MulAction.orbit K ω = MulAction.orbit H ω) : M = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x • ω ∈ MulAction.orbit K ω := by
    rw [horb]
    exact MulAction.mem_orbit ω x
  obtain ⟨k, hk⟩ := hx
  have h1 : (k : H)⁻¹ * x ∈ MulAction.stabilizer H ω := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hk]
    exact inv_smul_smul (k : H) ω
  have h2 := M.mul_mem (hK k.2) (hstab h1)
  rwa [mul_inv_cancel_left] at h2

theorem le_of_cover (ω : Ω) (S0 : Subgroup H) (Gs : Set H)
    (hcover : ∀ x : H, x ∈ S0 ∨ ∃ g ∈ Gs, ∃ h ∈ MulAction.stabilizer H ω, x • ω = (h * g) • ω)
    (hgen : ∀ g ∈ Gs, ∀ M : Subgroup H, MulAction.stabilizer H ω ≤ M → g ∈ M → M = ⊤)
    {M : Subgroup H} (hM : MulAction.stabilizer H ω ≤ M) (hMt : M ≠ ⊤) : M ≤ S0 := by
  intro x hx
  rcases hcover x with h0 | ⟨g, hg, h, hh, hxg⟩
  · exact h0
  · exfalso
    have h1 : (h * g)⁻¹ * x ∈ MulAction.stabilizer H ω := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hxg]
      exact inv_smul_smul (h * g) ω
    have h2 : h * g ∈ M := by
      have := M.mul_mem hx (M.inv_mem (hM h1))
      simpa using this
    have h3 : g ∈ M := by
      have := M.mul_mem (M.inv_mem (hM hh)) h2
      simpa using this
    exact hMt (hgen g hg M hM h3)

end Actions

section Sandwich

variable {G : Type} [Group G]

theorem conj_mem_of_blockStab_le {X R : Subgroup G} {t : G} {B : Set (Subgroup G)}
    {N : Subgroup G} (h : SandwichData X R t B N) (hR : IsUniqueInvolution R t)
    {S0 : Subgroup G} (hS : blockStab X B ≤ S0) {Zt : Set G}
    (hZ : ∀ m ∈ S0, m * t * m⁻¹ ∈ Zt) {x : G} (hx : x ∈ X) (hxN : x * t * x⁻¹ ∈ N) :
    x * t * x⁻¹ ∈ Zt := by
  obtain ⟨m, hm, he⟩ := h.inv_mem_conj hR hx hxN
  rw [he]
  exact hZ m (hS hm)

@[expose] def BadElt (T : Subgroup G) (K D : Set G) (x : G) : Prop :=
  ∃ d ∈ D, d ∈ Subgroup.closure (K ∪ {y | ∃ h ∈ T, y = h * x * h⁻¹})

theorem fixSet_anti {X : Subgroup G} {B B' : Set (Subgroup G)} (h : B ⊆ B') :
    fixSet X B' ≤ fixSet X B :=
  fun _ hα b hb y hy => hα b (h hb) y hy

end Sandwich

section Counting

variable {G : Type} [Group G]

private theorem relIndex_sup_right_aux {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : A.relIndex (B ⊔ A) = A.relIndex B := by
  have : (A.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have : (A.subgroupOf (B ⊔ A)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h).toEquiv).symm

private theorem card_sup_mul_card_inf_aux {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h2 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr (le_sup_right : A ≤ B ⊔ A), relIndex_sup_right_aux h] at h1
  rw [sup_comm, ← h1, ← h2]
  ring

private theorem card_dvd_of_normal_aux [Finite G] {T N S : Subgroup G} (hN : N ≤ T)
    (hnorm : T ≤ Subgroup.normalizer (N : Set G)) (hS : S ≤ T) {m : ℕ}
    (hT : Nat.card T ∣ Nat.card S * m) :
    Nat.card N ∣ Nat.card (N ⊓ S : Subgroup G) * m := by
  have e := card_sup_mul_card_inf_aux (A := N) (B := S) (hS.trans hnorm)
  have d : Nat.card (N ⊔ S : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le (sup_le hN hS)
  have hpos : 0 < Nat.card S := Nat.card_pos
  refine (Nat.mul_dvd_mul_iff_left hpos).1 ?_
  calc Nat.card S * Nat.card N = Nat.card (N ⊔ S : Subgroup G) * Nat.card (N ⊓ S : Subgroup G) := by
        rw [e]; ring
    _ ∣ (Nat.card S * m) * Nat.card (N ⊓ S : Subgroup G) :=
        Nat.mul_dvd_mul_right (d.trans hT) _
    _ = Nat.card S * (Nat.card (N ⊓ S : Subgroup G) * m) := by ring

theorem card_eq_mul_of_sylow [Finite G] {T N S2 S3 : Subgroup G} (hN : N ≤ T)
    (hNn : (N.subgroupOf T).Normal) (hS2 : S2 ≤ T) (hS3 : S3 ≤ T)
    (h2 : IsPGroup 2 S2) (h3 : IsPGroup 3 S3)
    (hT : Nat.card T = Nat.card S2 * Nat.card S3) :
    Nat.card N = Nat.card (N ⊓ S2 : Subgroup G) * Nat.card (N ⊓ S3 : Subgroup G) := by
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).1 hNn
  have i2 := card_dvd_of_normal_aux hN hnorm hS2 (m := Nat.card S3) hT.dvd
  have i3 := card_dvd_of_normal_aux hN hnorm hS3 (m := Nat.card S2)
    (by rw [hT]; exact dvd_of_eq (mul_comm _ _))
  obtain ⟨α, hα⟩ := IsPGroup.iff_card.1 h2
  obtain ⟨β, hβ⟩ := IsPGroup.iff_card.1 h3
  obtain ⟨γ, hγ⟩ := IsPGroup.iff_card.1 (h2.to_inf_right (H := N))
  obtain ⟨δ, hδ⟩ := IsPGroup.iff_card.1 (h3.to_inf_right (H := N))
  rw [hγ, hβ] at i2
  rw [hδ, hα] at i3
  have hcop : ∀ a b : ℕ, Nat.Coprime (3 ^ a) (2 ^ b) := fun a b =>
    Nat.Coprime.pow a b (by norm_num)
  have hle : Nat.card N ∣ 2 ^ γ * 3 ^ δ := by
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 i2
    have hk₂N : k₂ ∣ Nat.card N := Dvd.intro_left k₁ hk
    have hk₂' : k₂ ∣ 3 ^ δ :=
      (Nat.Coprime.coprime_dvd_left hk₂ (hcop β α)).dvd_of_dvd_mul_right (hk₂N.trans i3)
    rw [← hk]
    exact Nat.mul_dvd_mul hk₁ hk₂'
  have hge : 2 ^ γ * 3 ^ δ ∣ Nat.card N := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (hcop δ γ).symm ?_ ?_
    · rw [← hγ]
      exact Subgroup.card_dvd_of_le inf_le_left
    · rw [← hδ]
      exact Subgroup.card_dvd_of_le inf_le_left
  rw [hγ, hδ]
  exact Nat.dvd_antisymm hle hge

theorem card_le_of_pgroup_subset {p : ℕ} [Fact p.Prime] {V : Subgroup G} (hV : IsPGroup p V)
    [Finite V] {S : Set G} (hS : ∀ x ∈ V, x ∈ S) (hfin : S.Finite) {k : ℕ}
    (hk : S.ncard < p ^ (k + 1)) : Nat.card V ≤ p ^ k := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hV
  have h1 : Nat.card V ≤ S.ncard := by
    have hsub : (V : Set G) ⊆ S := hS
    calc Nat.card V = (V : Set G).ncard := (Nat.card_coe_set_eq (V : Set G)).symm
      _ ≤ S.ncard := Set.ncard_le_ncard hsub hfin
  rw [hn] at h1 ⊢
  have h2 : p ^ n < p ^ (k + 1) := lt_of_le_of_lt h1 hk
  have hn' : n < k + 1 := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).1 h2
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)

open scoped Pointwise in
theorem exists_conj_le_of_card [Finite G] {C S R : Subgroup G} (hS : S ≤ C) (hR : R ≤ C)
    (hR2 : IsPGroup 2 R) {k m : ℕ} (hSc : Nat.card S = 2 ^ k)
    (hCc : Nat.card C ∣ 2 ^ k * m) (hm : Odd m) : ∃ h ∈ C, conjSub h R ≤ S := by
  have hSp : IsPGroup 2 S := IsPGroup.iff_card.2 ⟨k, hSc⟩
  have hSp' : IsPGroup 2 (S.subgroupOf C) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hRp' : IsPGroup 2 (R.subgroupOf C) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf C).index := by
    have e := Subgroup.relIndex_mul_card S C
    rw [inf_of_le_left hS, hSc] at e
    have hd : S.relIndex C ∣ m := by
      refine (Nat.mul_dvd_mul_iff_right (by positivity : 0 < 2 ^ k)).1 ?_
      rw [e, mul_comm m]
      exact hCc
    have h1 := Nat.odd_iff.1 (hm.of_dvd_nat hd)
    intro h2
    have h2' : 2 ∣ S.relIndex C := h2
    omega
  let Q₀ : Sylow 2 C := hSp'.toSylow hidx
  obtain ⟨Q₁, hQ₁⟩ := hRp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q₁ Q₀
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  have hr' : (⟨r, hR hr⟩ : C) ∈ (Q₁ : Subgroup C) := hQ₁ (Subgroup.mem_subgroupOf.2 hr)
  have h1 : MulAut.conj g • (⟨r, hR hr⟩ : C) ∈ MulAut.conj g • (Q₁ : Subgroup C) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hr'
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  have h2 : (g * ⟨r, hR hr⟩ * g⁻¹ : C) ∈ (Q₀ : Subgroup C) := h1
  have h3 : (g * ⟨r, hR hr⟩ * g⁻¹ : C) ∈ S.subgroupOf C := h2
  exact h3

end Counting

section FixSet

private def conjTop (H : Type) [Group H] : H →* MulAut ↥(⊤ : Subgroup H) :=
  (MulAut.congr Subgroup.topEquiv.symm).toMonoidHom.comp MulAut.conj

private theorem conjTop_apply {H : Type} [Group H] (x : H) (y : ↥(⊤ : Subgroup H)) :
    ((conjTop H x y : ↥(⊤ : Subgroup H)) : H) = x * y * x⁻¹ := by
  simp [conjTop, MulAut.congr_apply]

private theorem conjTop_mem_fixSet_iff {H : Type} [Group H] (B : Set (Subgroup H)) (x : H) :
    conjTop H x ∈ fixSet (⊤ : Subgroup H) B ↔
      x ∈ Subgroup.centralizer {y : H | ∃ J ∈ B, y ∈ J} := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · rintro hx y ⟨J, hJ, hy⟩
    have h := congrArg (fun z : ↥(⊤ : Subgroup H) => (z : H)) (hx J hJ ⟨y, trivial⟩ hy)
    simp only [conjTop_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h b hb y hy
    apply Subtype.ext
    rw [conjTop_apply]
    have := h y ⟨b, hb, hy⟩
    calc x * (y : H) * x⁻¹ = (y * x) * x⁻¹ := by rw [this]
      _ = y := by group

theorem card_fixSet_mul_le {H : Type} [Group H] [Finite H] (B : Set (Subgroup H)) :
    Nat.card (fixSet (⊤ : Subgroup H) B) * Nat.card H ≤
      Nat.card (Subgroup.centralizer {x : H | ∃ J ∈ B, x ∈ J}) *
        Nat.card (MulAut ↥(⊤ : Subgroup H)) := by
  set F := fixSet (⊤ : Subgroup H) B with hF
  set R := (conjTop H).range with hR
  have hC : Subgroup.centralizer {x : H | ∃ J ∈ B, x ∈ J} = F.comap (conjTop H) := by
    ext x
    rw [Subgroup.mem_comap]
    exact (conjTop_mem_fixSet_iff B x).symm
  rw [hC]
  have hidx : R.relIndex F ≤ R.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  have h1 : Nat.card F ≤ R.index * Nat.card (R ⊓ F : Subgroup _) :=
    calc Nat.card F = R.relIndex F * Nat.card (R ⊓ F : Subgroup _) :=
          (Subgroup.relIndex_mul_card R F).symm
      _ ≤ R.index * Nat.card (R ⊓ F : Subgroup _) := Nat.mul_le_mul_right _ hidx
  have h3 : Nat.card H * Nat.card (F ⊓ R : Subgroup _) =
      Nat.card (F.comap (conjTop H)) * Nat.card R := by
    have e1 := Subgroup.relIndex_mul_card F R
    have e2 := Subgroup.index_mul_card (F.comap (conjTop H))
    rw [Subgroup.index_comap] at e2
    calc Nat.card H * Nat.card (F ⊓ R : Subgroup _)
        = F.relIndex R * Nat.card (F.comap (conjTop H)) * Nat.card (F ⊓ R : Subgroup _) := by
          rw [e2]
      _ = Nat.card (F.comap (conjTop H)) * (F.relIndex R * Nat.card (F ⊓ R : Subgroup _)) := by
          ring
      _ = Nat.card (F.comap (conjTop H)) * Nat.card R := by rw [e1]
  have h2 := Subgroup.index_mul_card R
  calc Nat.card F * Nat.card H
      ≤ R.index * Nat.card (R ⊓ F : Subgroup _) * Nat.card H := Nat.mul_le_mul_right _ h1
    _ = R.index * (Nat.card H * Nat.card (F ⊓ R : Subgroup _)) := by rw [inf_comm]; ring
    _ = Nat.card (F.comap (conjTop H)) * (R.index * Nat.card R) := by rw [h3]; ring
    _ = Nat.card (F.comap (conjTop H)) * Nat.card (MulAut ↥(⊤ : Subgroup H)) := by rw [h2]

end FixSet

section Core

variable {G : Type} [Group G]

theorem CoreData.conj_of_comm {R : Subgroup G} {t h : G}
    (hC : CoreData (⊤ : Subgroup G) R t) (hh : h * t = t * h) :
    CoreData (⊤ : Subgroup G) (conjSub h R) t := by
  have hT : h ∈ (⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_inf.2 ⟨trivial, Subgroup.mem_centralizer_singleton_iff.2 hh⟩
  refine ⟨le_top, ?_, ?_, hC.noncentral, ?_, ?_⟩
  · obtain ⟨e⟩ := hC.q8
    exact ⟨(Subgroup.equivMapOfInjective R (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective).symm.trans e⟩
  · have := hC.inv.conj h
    have e : h * t * h⁻¹ = t := by rw [hh]; group
    rwa [e] at this
  · obtain ⟨P, hP, hPn, hP2, hRP⟩ := hC.inO2
    refine ⟨P, hP, hPn, hP2, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hPn h hT r (hRP hr)
  · intro s hs
    have hs' : h⁻¹ * s * h ∈ (⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) :=
      ((⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)).mul_mem
        (((⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)).mul_mem
          (((⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)).inv_mem hT) hs) hT
    have e : conjSub s (conjSub h R) = conjSub h (conjSub (h⁻¹ * s * h) R) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [e]
    rcases hC.twins _ hs' with h1 | h1
    · left
      rw [h1]
    · right
      exact h1.conjSub h

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.OmGen

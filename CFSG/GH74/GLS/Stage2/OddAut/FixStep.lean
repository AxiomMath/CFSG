module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section FixStep

variable {Y : Type} [Group Y]

@[expose] def NoOddNormal (M : Subgroup Y) (r : ℕ) : Prop :=
  ∀ N : Subgroup Y, N ≤ M → (∀ c ∈ M, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
    (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) → Odd (Nat.card ↥N) → Nat.Coprime (Nat.card ↥N) r → N = ⊥

theorem noOddNormal_of_isPGroup [Finite Y] {r : ℕ} [Fact r.Prime] {M : Subgroup Y}
    (hM : IsPGroup r ↥M) : NoOddNormal M r := by
  intro N hNM _ _ _ hcop
  have hN : IsPGroup r ↥N := hM.to_le hNM
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  rw [hk] at hcop
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : Nat.Coprime r r := (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk0) r r).mp hcop
    exact (Fact.out : r.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 (dvd_refl r))
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

theorem noOddNormal_of_range {G : Type} [Group G] [Finite G] (φ : G →* Y)
    (hφ : Function.Injective φ)
    (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card ↥N) → N = ⊥) (r : ℕ) :
    NoOddNormal φ.range r := by
  intro N hNM hNn _ hodd _
  set N' : Subgroup G := N.comap φ with hN'
  have hnorm : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : φ n ∈ N := hn
    have := hNn (φ g) ⟨g, rfl⟩ (φ n) hn'
    show φ (g * n * g⁻¹) ∈ N
    simpa [map_mul, map_inv] using this
  have hcard : Nat.card ↥N' = Nat.card ↥N := by
    have h1 : N'.map φ = N := Subgroup.map_comap_eq_self hNM
    have h2 := Subgroup.card_map_of_injective (K := N') hφ
    rw [h1] at h2
    exact h2.symm
  have hbot := hG N' hnorm (hcard ▸ hodd)
  have h1 : Nat.card ↥N = 1 := by rw [← hcard, hbot]; simp
  exact Subgroup.card_eq_one.mp h1

theorem fix_step [Finite Y] {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (hcen : Subgroup.center Y = ⊥) (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z) {v : MulAut Y}
    (hv : v ∈ V) (hne : v ≠ 1) {M : Subgroup Y} (hMle : M ≤ fixSub v)
    (hMinv : ∀ z ∈ Z, ∀ c ∈ M, z c ∈ M) (hM : NoOddNormal M r) :
    ∀ z ∈ Z, ∀ c ∈ M, z c = c := by
  obtain ⟨-, -, -, -, hZab, hZodd, hZcop, -, -⟩ := h2
  have hinj := mulAut_conj_injective_of_center_bot hcen
  set N : Subgroup Y := M ⊓ Z.comap (MulAut.conj : Y →* MulAut Y) with hNdef
  have hNM : N ≤ M := inf_le_left
  have hNZ : ∀ n ∈ N, MulAut.conj n ∈ Z := fun n hn => hn.2
  have hnorm : ∀ c ∈ M, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    refine ⟨M.mul_mem (M.mul_mem hc (hNM hn)) (M.inv_mem hc), ?_⟩
    show MulAut.conj (c * n * c⁻¹) ∈ Z
    have h1 := (Subgroup.mem_normalizer_iff.mp (h3 v hv hne c (hMle hc))
      (MulAut.conj n)).mp (hNZ n hn)
    simpa [map_mul, map_inv] using h1
  have hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hZab _ (hNZ a ha) _ (hNZ b hb)
  have hdvd : Nat.card ↥N ∣ Nat.card ↥Z := by
    let ψ : ↥N →* ↥Z :=
      (((MulAut.conj : Y →* MulAut Y).comp N.subtype)).codRestrict Z (fun n => hNZ n.1 n.2)
    have hψ : Function.Injective ψ := by
      intro a b hab
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val hab
    exact Subgroup.card_dvd_of_injective ψ hψ
  have hNbot : N = ⊥ :=
    hM N hNM hnorm hab (Odd.of_dvd_nat hZodd hdvd) (Nat.Coprime.coprime_dvd_left hdvd hZcop)
  intro z hz c hc
  have hnormc := h3 v hv hne c (hMle hc)
  have h1 := (Subgroup.mem_normalizer_iff.mp hnormc z).mp hz
  have h4 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)
  have h5 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
    have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
      have := mulAut_conj_conj z c⁻¹
      simpa [map_inv] using this
    calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
        = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
      _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
  have hdN : c * z c⁻¹ ∈ N := by
    refine ⟨?_, ?_⟩
    · have := M.mul_mem hc (M.inv_mem (hMinv z hz c hc))
      simpa using this
    · show MulAut.conj (c * z c⁻¹) ∈ Z
      rw [← h5]
      exact h4
  rw [hNbot, Subgroup.mem_bot] at hdN
  have h6 : z c⁻¹ = c⁻¹ := by
    have := congrArg (fun t => c⁻¹ * t) hdN
    simpa using this
  have := congrArg (fun t => t⁻¹) h6
  simpa using this

end FixStep

section Ker

theorem exists_ne_one_mem_ker {A C : Type} [Group A] [Group C] [Finite A] [Finite C] [IsCyclic C]
    {r : ℕ} (hr : r.Prime) {V : Subgroup A} [IsElementaryAbelian r ↥V]
    (hVc : Nat.card ↥V = r ^ 2) (π : A →* C) : ∃ v ∈ V, v ≠ 1 ∧ π v = 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  let π' : ↥V →* C := π.comp V.subtype
  have hexp : ∀ x : ↥V, x ^ r = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p r ↥V) x
  have hrange : Nat.card ↥π'.range ≤ r := by
    have : Fintype C := Fintype.ofFinite C
    have h1 := IsCyclic.card_pow_eq_one_le (α := C) hr.pos
    let f : ↥π'.range → {a : C // a ^ r = 1} := fun x => ⟨x.1, by
      obtain ⟨y, hy⟩ := x.2
      rw [← hy, ← map_pow, hexp y, map_one]⟩
    have hf : Function.Injective f := fun a b hab => by
      have h := congrArg Subtype.val hab
      exact Subtype.ext h
    have h2 := Nat.card_le_card_of_injective f hf
    have h3 : Nat.card {a : C // a ^ r = 1} = (Finset.univ.filter fun a : C => a ^ r = 1).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h3] at h2
    exact h2.trans h1
  have hmul : Nat.card ↥π'.ker * Nat.card ↥π'.range = r ^ 2 := by
    have h := π'.ker.card_mul_index
    rw [Subgroup.index_ker, hVc] at h
    exact h
  have hker : π'.ker ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥π'.ker = 1 := by rw [hbot]; simp
    rw [h1, one_mul] at hmul
    have : r ^ 2 ≤ r := hmul ▸ hrange
    nlinarith [hr.one_lt]
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hker
  refine ⟨v.1, v.1.2, fun h => hv1 (Subtype.ext (Subtype.ext h)), ?_⟩
  exact v.2

end Ker

end CFSG.GH74.GLS.Stage2.OddAut

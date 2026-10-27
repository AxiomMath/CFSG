module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Prop
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups commutatorElement

section Perfect

variable {A : Type*} [Group A]

theorem perfectCore_eq_of_perfect [Finite A] {H J : Subgroup A} (hJH : J ≤ H) (hHJ : ⁅H, H⁆ ≤ J)
    (hJ : Group.IsPerfect ↥J) : ⁅H, H⁆ = J ∧ perfectCore H = J := by
  haveI := hJ
  have hJJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
  have h1 : ⁅H, H⁆ = J := le_antisymm hHJ (by
    calc J = ⁅J, J⁆ := hJJ.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hJH hJH)
  have hmap : ∀ n : ℕ, (derivedSeries ↥H (n + 1)).map H.subtype = J := by
    intro n
    induction n with
    | zero =>
      rw [zero_add, derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
        Subgroup.map_top, Subgroup.range_subtype]
      exact h1
    | succ n ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, ih, hJJ]
  refine ⟨h1, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥H = n + 1 :=
    ⟨Nat.card ↥H - 1, by have := Nat.card_pos (α := ↥H); omega⟩
  unfold perfectCore
  rw [hn]
  exact hmap n

end Perfect

section Conj

variable {A : Type*} [Group A] {T : Subgroup A} [T.Normal]

theorem conj_conjNormal {g : A} (hg : g ∈ T) (ψ : MulAut ↥T) :
    ψ * MulAut.conjNormal g * ψ⁻¹ = MulAut.conjNormal ((ψ ⟨g, hg⟩ : ↥T) : A) := by
  have h1 : MulAut.conjNormal (H := T) g = MulAut.conj (⟨g, hg⟩ : ↥T) :=
    MulAut.conjNormal_val (h := ⟨g, hg⟩)
  rw [h1, MulAut.conjNormal_val]
  ext t
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem map_conj_le {z : A} {ψ : MulAut ↥T}
    (hψ : ψ * MulAut.conjNormal z = MulAut.conjNormal z * ψ) :
    ((T ⊓ Subgroup.centralizer ({z} : Set A)).map (MulAut.conjNormal (H := T))).map
        (MulAut.conj ψ).toMonoidHom ≤
      (T ⊓ Subgroup.centralizer ({z} : Set A)).map (MulAut.conjNormal (H := T)) := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨hgT, hgz⟩ := Subgroup.mem_inf.mp hg
  refine ⟨((ψ ⟨g, hgT⟩ : ↥T) : A), Subgroup.mem_inf.mpr ⟨(ψ ⟨g, hgT⟩).2, ?_⟩, ?_⟩
  · have hgz' : z * g = g * z := Subgroup.mem_centralizer_singleton_iff.mp hgz |>.symm
    have h1 : MulAut.conjNormal z (⟨g, hgT⟩ : ↥T) = ⟨g, hgT⟩ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply, hgz']; group)
    have h2 := DFunLike.congr_fun hψ ⟨g, hgT⟩
    simp only [MulAut.mul_apply, h1] at h2
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (((ψ ⟨g, hgT⟩ : ↥T) : A)) * z = (z * ((ψ ⟨g, hgT⟩ : ↥T) : A) * z⁻¹) * z := by rw [← h3]
      _ = z * ((ψ ⟨g, hgT⟩ : ↥T) : A) := by group
  · rw [← conj_conjNormal hgT ψ]
    simp [MulAut.conj_apply]

theorem mem_normalizer_socSL {z : A}
    (hH : perfectCore (T ⊓ Subgroup.centralizer ({z} : Set A)) =
      ⁅T ⊓ Subgroup.centralizer ({z} : Set A), T ⊓ Subgroup.centralizer ({z} : Set A)⁆)
    {ψ : MulAut ↥T} (hψ : ψ * MulAut.conjNormal z = MulAut.conjNormal z * ψ) :
    ψ ∈ Subgroup.normalizer ((socSL T z : Subgroup (MulAut ↥T)) : Set (MulAut ↥T)) := by
  set Ĥ := (T ⊓ Subgroup.centralizer ({z} : Set A)).map (MulAut.conjNormal (H := T)) with hĤ
  have hsoc : socSL T z = ⁅Ĥ, Ĥ⁆ := by
    unfold socSL
    rw [hH, Subgroup.map_commutator]
  have key : ∀ ψ' : MulAut ↥T, ψ' * MulAut.conjNormal z = MulAut.conjNormal z * ψ' →
      ∀ x ∈ ⁅Ĥ, Ĥ⁆, ψ' * x * ψ'⁻¹ ∈ ⁅Ĥ, Ĥ⁆ := by
    intro ψ' hψ' x hx
    have h1 := map_conj_le hψ'
    have h2 : ⁅Ĥ, Ĥ⁆.map (MulAut.conj ψ').toMonoidHom ≤ ⁅Ĥ, Ĥ⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono h1 h1
    simpa [MulAut.conj_apply] using h2 ⟨x, hx, rfl⟩
  have hψ' : ψ⁻¹ * MulAut.conjNormal z = MulAut.conjNormal z * ψ⁻¹ :=
    (Commute.inv_left (show Commute ψ (MulAut.conjNormal z) from hψ))
  rw [hsoc, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key ψ hψ x, fun hx => ?_⟩
  have := key ψ⁻¹ hψ' _ hx
  have h3 : ψ⁻¹ * (ψ * x * ψ⁻¹) * ψ⁻¹⁻¹ = x := by group
  rwa [h3] at this

end Conj

section Odd

theorem odd_relIndex_of_two_elts {G : Type*} [Group G] [Finite G] {N Y : Subgroup G}
    (h2 : ∀ s ∈ Y, ∀ k : ℕ, s ^ 2 ^ k = 1 → s ∈ N) : Odd (N.relIndex Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  have hP : (P : Subgroup ↥Y) ≤ N.subgroupOf Y := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf]
    refine h2 x x.2 k ?_
    have h1 := congrArg (fun y : ↥P => ((y : ↥Y) : G)) hk
    simpa using h1
  have h1 : (N.subgroupOf Y).index ∣ (P : Subgroup ↥Y).index := Subgroup.index_dvd_of_le hP
  have h3 : ¬ 2 ∣ (P : Subgroup ↥Y).index := P.not_dvd_index
  rw [Subgroup.relIndex]
  by_contra hev
  exact h3 ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)).trans h1)

end Odd

section Assemble

theorem socF4_clause_of_parts {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal]
    {R : Subgroup A} {S : Sylow 2 R} {z : A} (hzS : z ∈ sylowSet S) {J : Subgroup A}
    (hJH : J ≤ T ⊓ Subgroup.centralizer ({z} : Set A))
    (hHJ : ⁅T ⊓ Subgroup.centralizer ({z} : Set A), T ⊓ Subgroup.centralizer ({z} : Set A)⁆ ≤ J)
    (hJ : Group.IsPerfect ↥J) (hJS : ∀ y ∈ J, ∀ s ∈ sylowSet S, y * s = s * y)
    (h2 : ∀ ψ ∈ autCentOf T (sylowSet S), ∀ k : ℕ, ψ ^ 2 ^ k = 1 →
      ψ ∈ J.map (MulAut.conjNormal (H := T)))
    {K : Type} [Field K] [Finite K] (hKodd : Odd (Nat.card K)) (hK4 : 4 ≤ Nat.card K)
    (Φ : SL(2, K) →* MulAut ↥T) (hΦ : Function.Injective Φ)
    (hΦr : Φ.range = J.map (MulAut.conjNormal (H := T))) :
    socSL T z ≤ autCentOf T (sylowSet S) ∧
      autCentOf T (sylowSet S) ≤ Subgroup.normalizer ((socSL T z : Subgroup (MulAut ↥T)) :
        Set (MulAut ↥T)) ∧
      Odd ((socSL T z).relIndex (autCentOf T (sylowSet S))) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧ 4 ≤ Nat.card K ∧
        Nonempty (↥(socSL T z) ≃* SL(2, K)) := by
  obtain ⟨hcomm, hpc⟩ := perfectCore_eq_of_perfect hJH hHJ hJ
  have hsoc : socSL T z = J.map (MulAut.conjNormal (H := T)) := by
    unfold socSL
    rw [hpc]
  have h1 : socSL T z ≤ autCentOf T (sylowSet S) := by
    rw [hsoc]
    rintro _ ⟨y, hy, rfl⟩
    exact conjNormal_mem_autCentOf fun s hs => hJS y hy s hs
  refine ⟨h1, fun ψ hψ => ?_, ?_, K, inferInstance, inferInstance, hKodd, hK4, ⟨?_⟩⟩
  · exact mem_normalizer_socSL (hpc.trans hcomm.symm) ((mem_autCentOf_iff.mp hψ) z hzS)
  · exact odd_relIndex_of_two_elts fun s hs k hk => by
      rw [hsoc]
      exact h2 s hs k hk
  · exact (MulEquiv.subgroupCongr (hsoc.trans hΦr.symm)).trans (MonoidHom.ofInjective hΦ).symm

end Assemble

section Mem

theorem z_mem_of_comm2 {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A] {T : Subgroup A}
    [T.Normal] (hC : Subgroup.centralizer (T : Set A) = ⊥) (hcomm : SocleComm2 ↥T) {R : Subgroup A}
    {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) (hc : TightClsR r A R S z) :
    z ∈ T ∧ z ∈ sylowSet S := by
  obtain ⟨x, b, hx, hb, hq, hxz⟩ := exists_qrel8_of_datum hr hd hc
  have hz2 : z * z = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
  have hzS : z ∈ sylowSet S := hxz ▸ (sylowSet S).pow_mem hx 4
  have hP : IsPGroup 2 (sylowSet S) := S.isPGroup'.map _
  have hle := hcomm A T ‹T.Normal› ⟨MulEquiv.refl _⟩ hC (sylowSet S) hP
  have hcm : ⁅b, x ^ 2⁆ ∈ T :=
    hle (Subgroup.commutator_mem_commutator hb ((sylowSet S).pow_mem hx 2))
  have hb2 : b * x ^ 2 * b⁻¹ = (x ^ 2)⁻¹ := by
    rw [← inv_pow, ← hq.bx, conj_pow]
  have h1 : ⁅b, x ^ 2⁆ = z⁻¹ := by
    rw [commutatorElement_def, hb2, ← mul_inv_rev, ← pow_add, ← hxz]
  refine ⟨?_, hzS⟩
  rw [h1] at hcm
  simpa using T.inv_mem hcm

end Mem

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

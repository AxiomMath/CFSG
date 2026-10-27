module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

section Strong

variable {X : Type} [Group X]

theorem noStronglyClosedElemAbelian_of_witnesses [Finite X] (Q₀ : Subgroup X)
    (hQ₀ : IsSylowTwoOf Q₀ ⊤)
    (hw : ∀ z ∈ Q₀, z ≠ 1 → (∀ q ∈ Q₀, q * z = z * q) →
      ∃ g h : X, g⁻¹ * z * g ∈ Q₀ ∧ h⁻¹ * z * h ∈ Q₀ ∧
        (g⁻¹ * z * g) * (h⁻¹ * z * h) ≠ (h⁻¹ * z * h) * (g⁻¹ * z * g)) :
    NoStronglyClosedElemAbelian X := by
  refine noStronglyClosedElemAbelian_of_sylow Q₀ hQ₀ ?_
  intro A hW
  by_contra hne
  have hQ2 : IsPGroup 2 Q₀ := (isSylowTwoOf_top_iff.mp hQ₀).1
  have hAn : ∀ a ∈ A, ∀ q ∈ Q₀, q⁻¹ * a * q ∈ A := fun a ha q hq =>
    hW.closed a ha q (mul_mem (mul_mem (inv_mem hq) (hW.le ha)) hq)
  obtain ⟨z, hzA, hz1, hzc⟩ := exists_ne_one_mem_centralizer hQ2 hW.le hAn hne
  obtain ⟨g, h, hg, hh, hne'⟩ := hw z (hW.le hzA) hz1 hzc
  have h1 := hW.closed z hzA g hg
  have h2 := hW.closed z hzA h hh
  exact hne' (congrArg Subtype.val
    (hW.elem.1.is_comm.comm (⟨_, h1⟩ : A) (⟨_, h2⟩ : A)))

theorem sylowCentralizingAutInner_of_opposite [Finite X] {UC VC : Subgroup X}
    (hU : IsSylowTwoOf UC ⊤) (hV : IsSylowTwoOf VC ⊤) (hUV : UC ⊓ VC = ⊥)
    (hopp : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → UC ⊓ S = ⊥ →
      ∃ u ∈ UC, S = VC.map (MulAut.conj u).toMonoidHom)
    (hrigid : ∀ δ : X ≃* X, UC.map δ.toMonoidHom = UC → VC.map δ.toMonoidHom = VC →
      (∃ w ∈ UC, ∀ x ∈ UC, δ x = w * x * w⁻¹) → δ = 1) :
    SylowCentralizingAutInner X := by
  refine sylowCentralizingAutInner_of_sylow UC hU ?_
  intro β hβ
  have hβU : UC.map β.toMonoidHom = UC := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hβ y hy]
    · intro hx
      exact ⟨x, hx, hβ x hx⟩
  have hS : IsSylowTwoOf (VC.map β.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hV
    refine isSylowTwoOf_top_iff.mpr ⟨hp.map β.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := β.toMonoidHom) β.bijective]
    exact hi
  have hUS : UC ⊓ VC.map β.toMonoidHom = ⊥ := by
    rw [← hβU, ← Subgroup.map_inf_eq _ _ _ β.injective, hUV, Subgroup.map_bot]
  obtain ⟨u, hu, hSu⟩ := hopp _ hS hUS
  let δ : X ≃* X := β.trans (MulAut.conj u⁻¹)
  have hδx : ∀ x, δ x = u⁻¹ * β x * u := fun x => by
    simp [δ]
  have hδU : UC.map δ.toMonoidHom = UC := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hδx, hβ y hy]
      exact mul_mem (mul_mem (inv_mem hu) hy) hu
    · intro hx
      refine ⟨u * x * u⁻¹, mul_mem (mul_mem hu hx) (inv_mem hu), ?_⟩
      rw [hδx, hβ _ (mul_mem (mul_mem hu hx) (inv_mem hu))]
      group
  have hδV : VC.map δ.toMonoidHom = VC := by
    have h1 : VC.map δ.toMonoidHom =
        (VC.map β.toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, hSu, Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨x, hx, by simp [mul_assoc]⟩
  have hδ1 : δ = 1 := hrigid δ hδU hδV ⟨u⁻¹, inv_mem hu, fun x hx => by
    rw [hδx, hβ x hx]
    simp⟩
  refine ⟨u⁻¹, fun y => ?_⟩
  have h := congrArg (fun φ : X ≃* X => φ y) hδ1
  simp only [MulAut.one_apply] at h
  rw [hδx] at h
  calc β y = u * (u⁻¹ * β y * u) * u⁻¹ := by group
    _ = u * y * u⁻¹ := by rw [h]
    _ = (u⁻¹)⁻¹ * y * u⁻¹ := by rw [inv_inv]

theorem eq_of_conj_eq_of_complement {G : Type*} [Group G] {I : Type*} {U N : Subgroup G}
    (x : I → G) (hNU : N ≤ U) (hNn : (N.subgroupOf U).Normal) (hxU : ∀ c, x c ∈ U)
    (hxc : ∀ c c', x c * x c' = x c' * x c)
    (hdec : (U : Set G) = Set.range x * (N : Set G))
    (huniq : ∀ n ∈ N, ∀ n' ∈ N, ∀ c c', n * x c = n' * x c' → n = n' ∧ c = c')
    {w : G} (hw : w ∈ U) {c c' : I} (h : w * x c * w⁻¹ = x c') : c' = c := by
  have hconj : ∀ n ∈ N, ∀ u ∈ U, u * n * u⁻¹ ∈ N := fun n hn u hu =>
    Subgroup.mem_subgroupOf.mp (hNn.conj_mem ⟨n, hNU hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
      ⟨u, hu⟩)
  obtain ⟨_, ⟨e, rfl⟩, b, hb, hab⟩ : w ∈ Set.range x * (N : Set G) := hdec ▸ hw
  have hn1 : b * (x c * b⁻¹ * (x c)⁻¹) ∈ N :=
    mul_mem hb (hconj b⁻¹ (inv_mem hb) (x c) (hxU c))
  have hn2 : x e * (b * (x c * b⁻¹ * (x c)⁻¹)) * (x e)⁻¹ ∈ N := hconj _ hn1 (x e) (hxU e)
  have hcomm : x e * x c * (x e)⁻¹ = x c := by rw [hxc e c]; group
  have hw' : w * x c * w⁻¹ = (x e * (b * (x c * b⁻¹ * (x c)⁻¹)) * (x e)⁻¹) * x c := by
    rw [← hab]
    calc x e * b * x c * (x e * b)⁻¹ =
        x e * (b * (x c * b⁻¹ * (x c)⁻¹) * x c) * (x e)⁻¹ := by group
      _ = (x e * (b * (x c * b⁻¹ * (x c)⁻¹)) * (x e)⁻¹) * (x e * x c * (x e)⁻¹) := by group
      _ = (x e * (b * (x c * b⁻¹ * (x c)⁻¹)) * (x e)⁻¹) * x c := by rw [hcomm]
  have h1 : (x e * (b * (x c * b⁻¹ * (x c)⁻¹)) * (x e)⁻¹) * x c = 1 * x c' := by
    rw [← hw', h, one_mul]
  exact (huniq _ hn2 1 (one_mem N) c c' h1).2.symm

theorem exists_ne_zero_one {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  have hcard : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨ω, hω.1, hω.2⟩

end Strong

theorem centralizes_of_mulEquiv {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {Y : Type} [Group Y]
    (e : L ⧸ Subgroup.center L ≃* Y) (hX : NoStronglyClosedElemAbelian Y)
    (hA : SylowCentralizingAutInner Y) {w : G} (hwU : w ∈ U)
    (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) :=
  centralizes_of_family h (hX.of_mulEquiv e) (hA.of_mulEquiv e) hwU hwS

end CFSG.QuasithinUnique.K1

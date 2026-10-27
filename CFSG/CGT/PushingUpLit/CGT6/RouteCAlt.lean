module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCPerm
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLift
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Coinv
public import CFSG.CGT.PushingUpLit.CGT6.EmbEight
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

section Aux

variable {V : Type} [CommGroup V]

theorem commV_invariant_normalizer {N : Subgroup (MulAut V)} {x : MulAut V}
    (hx : x ∈ Subgroup.normalizer (N : Set (MulAut V))) {w : V} (hw : w ∈ commV N) :
    x w ∈ commV N :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hx hw

end Aux

structure AltData {V : Type} [CommGroup V] (y d t : MulAut V) (a : ℕ) where
  w : Fin (2 * a + 1) → V
  injective : Function.Injective w
  span : Subgroup.closure (Set.range w) = ⊤
  py : Equiv.Perm (Fin (2 * a + 1))
  pd : Equiv.Perm (Fin (2 * a + 1))
  pe : Equiv.Perm (Fin (2 * a + 1))
  hpy : ∀ i, y (w i) = w (py i)
  hpd : ∀ i, d (w i) = w (pd i)
  hpe : ∀ i, (t * d * t⁻¹) (w i) = w (pe i)
  hpt : ∀ i, ∃ j, t (w i) = w j
  three : py.IsThreeCycle
  trans : ∀ i j, ∃ p ∈ Subgroup.closure ({py, pd, pe} : Set (Equiv.Perm (Fin (2 * a + 1)))),
    p i = j
  fix : ∀ v : V, y v = v → d v = v → (t * d * t⁻¹) v = v → v = 1
  ne_one : w ⟨0, by omega⟩ ≠ 1

section Alt

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.lift_of_alt (hNL : NatLiftStatement) (hNR : NatRecogStatement)
    (hV : ∀ v : V, v ^ 2 = 1) (cfg : Emb5Cfg G T Y) {y d t : MulAut V}
    (hY : Y = Subgroup.zpowers y) (hdN : d ∈ conjClosure Y G) (htG : t ∈ G) (ht2 : t ^ 2 = 1)
    (hgen : Subgroup.zpowers d ⊔ Y ⊔ Subgroup.zpowers t = G) {a : ℕ} (ha : 2 ≤ a)
    (hprime : (2 * a + 1).Prime) (D : AltData y d t a) :
    ∃ X, Lift5 G Y X := by
  classical
  obtain ⟨w, hw, hspan, py, pd, pe, hpy, hpd, hpe, hpt, h3, htrans, hfix, hw0⟩ := D
  have hyperm : y ∈ permSet hw := fun i => ⟨py i, hpy i⟩
  have hdperm : d ∈ permSet hw := fun i => ⟨pd i, hpd i⟩
  have heperm : t * d * t⁻¹ ∈ permSet hw := fun i => ⟨pe i, hpe i⟩
  have htperm : t ∈ permSet hw := hpt
  have hGperm : G ≤ permSet hw := by
    rw [← hgen]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hdperm)
      (hY ▸ Subgroup.zpowers_le.mpr hyperm)) (Subgroup.zpowers_le.mpr htperm)
  have hYG : Y ≤ G := by
    rw [← hgen]
    exact le_sup_of_le_left le_sup_right
  set N := conjClosure Y G with hN
  have hNG : N ≤ G := conjClosure_le hYG
  have hNperm : N ≤ permSet hw := hNG.trans hGperm
  have hYN : Y ≤ N := le_conjClosure
  have hyN : y ∈ N := hYN (hY ▸ Subgroup.mem_zpowers y)
  let ψ : ↥N →* Equiv.Perm (Fin (2 * a + 1)) :=
    (permSetHom hw).comp (Subgroup.inclusion hNperm)
  have hψspec : ∀ (x : ↥N) i, (x : MulAut V) (w i) = w (ψ x i) := fun x i =>
    permSetHom_spec hw ⟨x, hNperm x.2⟩ i
  have hψy : ψ ⟨y, hyN⟩ = py :=
    Equiv.ext fun i => (permSetHom_apply_eq_iff hw ⟨y, hyperm⟩).mpr (hpy i)
  have hψd : ψ ⟨d, hdN⟩ = pd :=
    Equiv.ext fun i => (permSetHom_apply_eq_iff hw ⟨d, hdperm⟩).mpr (hpd i)
  have hNnorm : ∀ x ∈ G, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (Y := Y) hx) n).mp hn
  have heN : t * d * t⁻¹ ∈ N := hNnorm t htG d hdN
  have hψe : ψ ⟨t * d * t⁻¹, heN⟩ = pe :=
    Equiv.ext fun i => (permSetHom_apply_eq_iff hw ⟨t * d * t⁻¹, heperm⟩).mpr (hpe i)
  have hcl : Subgroup.closure ({py, pd, pe} : Set (Equiv.Perm (Fin (2 * a + 1)))) ≤ ψ.range := by
    rw [Subgroup.closure_le]
    intro q hq
    rcases hq with rfl | hq
    · exact ⟨⟨y, hyN⟩, hψy⟩
    · rcases hq with rfl | hq
      · exact ⟨⟨d, hdN⟩, hψd⟩
      · rw [Set.mem_singleton_iff] at hq
        rw [hq]
        exact ⟨⟨t * d * t⁻¹, heN⟩, hψe⟩
  let sgn : ↥(permSet hw) →* ℤˣ := Equiv.Perm.sign.comp (permSetHom hw)
  have hsgny : ∀ (y' : MulAut V) (hy' : y' ∈ Y) (h : y' ∈ permSet hw), sgn ⟨y', h⟩ = 1 := by
    intro y' hy' h
    rw [hY] at hy'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have hzp : (⟨y ^ m, h⟩ : ↥(permSet hw)) = (⟨y, hyperm⟩ : ↥(permSet hw)) ^ m := rfl
    have h1 : sgn ⟨y, hyperm⟩ = 1 := by
      show Equiv.Perm.sign (permSetHom hw ⟨y, hyperm⟩) = 1
      have : permSetHom hw ⟨y, hyperm⟩ = py := hψy
      rw [this]
      exact h3.sign
    rw [hzp, map_zpow, h1, one_zpow]
  let E : Subgroup (MulAut V) := sgn.ker.map (permSet hw).subtype
  have hNE : N ≤ E := by
    rw [hN, conjClosure, Subgroup.closure_le]
    rintro _ ⟨g', hg', y', hy', rfl⟩
    have hg'p : g' ∈ permSet hw := hGperm hg'
    have hy'p : y' ∈ permSet hw := hNperm (hYN hy')
    refine ⟨⟨g', hg'p⟩ * ⟨y', hy'p⟩ * ⟨g', hg'p⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_comm (sgn ⟨g', hg'p⟩),
      mul_assoc, mul_inv_cancel, mul_one]
    exact hsgny y' hy' hy'p
  have hsignN : ∀ x : ↥N, Equiv.Perm.sign (ψ x) = 1 := by
    intro x
    obtain ⟨z, hz, hzx⟩ := hNE x.2
    have hzeq : z = ⟨(x : MulAut V), hNperm x.2⟩ := Subtype.ext hzx
    rw [hzeq] at hz
    exact hz
  let ψ' : ↥N →* ↥(alternatingGroup (Fin (2 * a + 1))) :=
    ψ.codRestrict _ (fun x => Equiv.Perm.mem_alternatingGroup.mpr (hsignN x))
  have hrange : alternatingGroup (Fin (2 * a + 1)) ≤ ψ.range := by
    have hpyR : py ∈ ψ.range := ⟨⟨y, hyN⟩, hψy⟩
    have htr : MulAction.IsPretransitive ↥ψ.range (Fin (2 * a + 1)) :=
      ⟨fun i j => by
        obtain ⟨p, hp, hpij⟩ := htrans i j
        exact ⟨⟨p, hcl hp⟩, hpij⟩⟩
    have hprim : MulAction.IsPreprimitive ↥ψ.range (Fin (2 * a + 1)) :=
      MulAction.IsPreprimitive.of_prime_card (by rwa [Nat.card_eq_fintype_card, Fintype.card_fin])
    exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hpyR
  have hψinj : Function.Injective ψ := fun x x' h => by
    have h1 := permSetHom_injective hw hspan (a₁ := ⟨x, hNperm x.2⟩) (a₂ := ⟨x', hNperm x'.2⟩) h
    have h2 := congrArg (Subtype.val : ↥(permSet hw) → MulAut V) h1
    exact Subtype.ext h2
  have hbij : Function.Bijective ψ' := by
    refine ⟨fun x x' h => hψinj (congrArg Subtype.val h), fun σ => ?_⟩
    obtain ⟨x, hx⟩ := hrange (Equiv.Perm.mem_alternatingGroup.mpr σ.2)
    exact ⟨x, Subtype.ext hx⟩
  let θ : ↥N ≃* ↥(alternatingGroup (Fin (2 * a + 1))) := MulEquiv.ofBijective ψ' hbij
  have hθ : ∀ x : ↥N, ((θ x : ↥(alternatingGroup (Fin (2 * a + 1)))) :
      Equiv.Perm (Fin (2 * a + 1))) = ψ x := fun x => rfl
  have hCV : ∀ v : V, (∀ x : ↥N, (x : MulAut V) v = v) → v = 1 := by
    intro v hv
    exact hfix v (hv ⟨y, hyN⟩) (hv ⟨d, hdN⟩) (hv ⟨t * d * t⁻¹, hNnorm t htG d hdN⟩)
  let i₀ : Fin (2 * a + 1) := ⟨0, by omega⟩
  have hJ : ∀ x : ↥N, θ x ∈ altStabilizer (2 * a + 1) {i₀} → (x : MulAut V) (w i₀) = w i₀ := by
    intro x hx
    rw [mem_altStabilizer_iff] at hx
    have h1 := hx i₀ (Finset.mem_singleton_self i₀)
    rw [hθ] at h1
    rw [hψspec x i₀, h1]
  have hnat := hNR V hV N a ha θ hCV i₀ (w i₀) hw0 hJ
  have horb : orbitSpan N (w i₀) = ⊤ := by
    rw [eq_top_iff, ← hspan, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨p, hp, hpi⟩ := htrans i₀ i
    obtain ⟨x, hx⟩ := hcl hp
    refine Subgroup.subset_closure ⟨(x : MulAut V), x.2, ?_⟩
    rw [hψspec x i₀, hx, hpi]
  have hcommN : commV N = ⊤ := by
    have hGle : G ≤ N ⊔ Subgroup.zpowers t := by
      rw [← hgen]
      exact sup_le (sup_le (le_sup_of_le_left (Subgroup.zpowers_le.mpr hdN))
        (le_sup_of_le_left hYN)) le_sup_right
    have h1 : commV G ≤ commV N ⊔ commV (Subgroup.zpowers t) :=
      (commV_mono hGle).trans (commV_sup_le N (Subgroup.zpowers t))
    rw [cfg.comm, top_le_iff] at h1
    have hzt : Subgroup.zpowers t ≤ G := Subgroup.zpowers_le.mpr htG
    exact eq_top_of_sup_commV_eq_top hV (isPGroup_zpowers_of_sq ht2)
      (fun x hx w' hw' => commV_invariant_normalizer
        (le_normalizer_conjClosure (Y := Y) (hzt hx)) hw') h1
  have hnat' : IsNatSectionWith (altAct (2 * a + 1)) θ (commV N) ⊥ := by
    rw [hcommN, ← horb]
    exact hnat
  have hYsub : Y.subgroupOf N = Subgroup.zpowers (⟨y, hyN⟩ : ↥N) := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf, hY]
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, Subtype.ext hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  have hθy : θ ⟨y, hyN⟩ = (⟨py, h3.mem_alternatingGroup⟩ : ↥(alternatingGroup (Fin (2 * a + 1)))) :=
    Subtype.ext hψy
  have hYmap : (Y.subgroupOf N).map θ.toMonoidHom =
      altStabilizer (2 * a + 1) (Finset.univ \ py.support) := by
    rw [hYsub, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hθy,
      altStabilizer_eq_zpowers_of_isThreeCycle (π := ⟨py, h3.mem_alternatingGroup⟩) h3]
  have hF : (Finset.univ \ py.support).card = (2 * a + 1) - (2 * 1 + 1) := by
    rw [Finset.card_univ_sdiff, h3.card_support, Fintype.card_fin]
  obtain ⟨hX, harr⟩ := hNL V hV N Y a 1 ha le_rfl (by omega) θ hnat' _ hF hYN hYmap
  have hNn : ((N.subgroupOf G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).2 le_normalizer_conjClosure
  exact ⟨N, hYN, hNG, hNn.isSubnormal, hX, harr⟩

end Alt

end CFSG.CGT.PushingUpLit.CGT6

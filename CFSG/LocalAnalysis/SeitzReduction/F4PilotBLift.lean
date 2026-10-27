module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftGomi
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)

section Commutators

variable {X : Type*} [Group X]

theorem le_commutator_zpowers_of_isQuasisimple {E : Subgroup X} (hE : CFSG.IsQuasisimple E)
    {x : X} (hx : x ∈ normalizer (E : Set X)) (hxE : x ∉ centralizer (E : Set X)) :
    E ≤ ⁅E, zpowers x⁆ := by
  have hCE : ⁅E, zpowers x⁆ ≤ E := le_normalizer_iff_commutator_le_left.1 (zpowers_le.2 hx)
  have hCn : (⁅E, zpowers x⁆.subgroupOf E).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCE).2 (normalizer_commutator_ge_left E (zpowers x))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hCn with htop | hcen
  · intro y hy
    have : (⟨y, hy⟩ : E) ∈ ⁅E, zpowers x⁆.subgroupOf E := htop ▸ mem_top _
    exact mem_subgroupOf.1 this
  · exfalso
    apply hxE
    have hCc : ⁅E, zpowers x⁆ ≤ centralizer (E : Set X) := fun c hc => by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := mem_center_iff.1 (hcen (mem_subgroupOf.2 (show ((⟨c, hCE hc⟩ : E) : X) ∈ _
        from hc))) ⟨y, hy⟩
      exact congrArg Subtype.val h1
    have hbot := CFSG.LocalCores.perfect_double_commutator hE.1
      (commutator_eq_bot_iff_le_centralizer.2 hCc)
    have hEx := commutator_eq_bot_iff_le_centralizer.1 hbot
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.1 (hEx hy) x (mem_zpowers x)).symm

theorem sup_conj_le_commutator_zpowers {K : Subgroup X} (hK : ⁅K, K⁆ = K) {x : X}
    (hcomm : ⁅K, K.map (MulAut.conj x).toMonoidHom⁆ = ⊥) :
    K ⊔ K.map (MulAut.conj x).toMonoidHom ≤
      ⁅K ⊔ K.map (MulAut.conj x).toMonoidHom, zpowers x⁆ := by
  set Kx := K.map (MulAut.conj x).toMonoidHom with hKx
  set N := ⁅K ⊔ Kx, zpowers x⁆ with hN
  have hNn : K ⊔ Kx ≤ normalizer (N : Set X) := normalizer_commutator_ge_left _ _
  have hcK : ∀ k ∈ K, ∀ y ∈ Kx, k * y = y * k := fun k hk y hy => by
    have := commutator_eq_bot_iff_le_centralizer.1 hcomm hk
    exact (mem_centralizer_iff.1 this y hy).symm
  have hKN : K ≤ N := by
    rw [← hK, commutator_le]
    intro k₁ hk₁ k₂ hk₂
    have hc : ⁅k₂, x⁆ ∈ N := commutator_mem_commutator (mem_sup_left hk₂) (mem_zpowers x)
    have hconj := (mem_normalizer_iff.1 (hNn (mem_sup_left hk₁)) _).1 hc
    have hy : x * k₂⁻¹ * x⁻¹ ∈ Kx := ⟨k₂⁻¹, K.inv_mem hk₂, by simp [MulAut.conj_apply]⟩
    have e1 : k₁ * ⁅k₂, x⁆ * k₁⁻¹ * ⁅k₂, x⁆⁻¹ = ⁅k₁, k₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have h1 := hcK k₁ hk₁ _ hy
      have h2 : x * k₂⁻¹ * x⁻¹ * k₁⁻¹ = k₁⁻¹ * (x * k₂⁻¹ * x⁻¹) := by
        have := hcK k₁⁻¹ (K.inv_mem hk₁) _ hy
        exact this.symm
      calc k₁ * (k₂ * x * k₂⁻¹ * x⁻¹) * k₁⁻¹ * (k₂ * x * k₂⁻¹ * x⁻¹)⁻¹
          = k₁ * k₂ * (x * k₂⁻¹ * x⁻¹ * k₁⁻¹) * (x * k₂⁻¹ * x⁻¹)⁻¹ * k₂⁻¹ := by group
        _ = k₁ * k₂ * (k₁⁻¹ * (x * k₂⁻¹ * x⁻¹)) * (x * k₂⁻¹ * x⁻¹)⁻¹ * k₂⁻¹ := by rw [h2]
        _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by group
    rw [← e1]
    exact N.mul_mem hconj (N.inv_mem hc)
  have hxN : x ∈ normalizer (N : Set X) := normalizer_commutator_ge_right _ _ (mem_zpowers x)
  have hKxN : Kx ≤ N := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.1 hxN k).1 (hKN hk)
  exact sup_le hKN hKxN

end Commutators

section Lift

variable {H : Type*} [Group H]

@[expose] def oddCoreLift (E : Subgroup (H ⧸ oddCore H)) : Subgroup H :=
  perfectCore (E.comap (QuotientGroup.mk' (oddCore H)))

@[expose] def HasBLift (E : Subgroup (H ⧸ oddCore H)) : Prop :=
  oddCoreLift E ≤ centralizer (oddCore H : Set H)

theorem hasBLift_iff {E : Subgroup (H ⧸ oddCore H)} :
    HasBLift E ↔ oddCoreLift E ≤ centralizer (oddCore H : Set H) :=
  Iff.rfl

theorem oddCoreLift_le_comap (E : Subgroup (H ⧸ oddCore H)) :
    oddCoreLift E ≤ E.comap (QuotientGroup.mk' (oddCore H)) :=
  perfectCore_le _

theorem oddCoreLift_mono {E₁ E₂ : Subgroup (H ⧸ oddCore H)} (h : E₁ ≤ E₂) :
    oddCoreLift E₁ ≤ oddCoreLift E₂ :=
  CFSG.Quasithin.perfectCore_mono (comap_mono h)

theorem HasBLift.mono {E₁ E₂ : Subgroup (H ⧸ oddCore H)} (h : E₁ ≤ E₂) (h₂ : HasBLift E₂) :
    HasBLift E₁ :=
  (oddCoreLift_mono h).trans h₂

theorem mem_normalizer_oddCoreLift (E : Subgroup (H ⧸ oddCore H)) {x : H}
    (hx : QuotientGroup.mk' (oddCore H) x ∈ normalizer (E : Set (H ⧸ oddCore H))) :
    x ∈ normalizer (oddCoreLift E : Set H) :=
  CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (le_normalizer_comap _ hx)

theorem le_oddCoreLift_of_perfect {E : Subgroup (H ⧸ oddCore H)} {P : Subgroup H}
    (hP : ⁅P, P⁆ = P) (hPE : P.map (QuotientGroup.mk' (oddCore H)) ≤ E) : P ≤ oddCoreLift E :=
  CFSG.Quasithin.le_perfectCore_of_perfect (map_le_iff_le_comap.1 hPE) hP

theorem HasBLift.le_centralizer_of_perfect {E : Subgroup (H ⧸ oddCore H)} (h : HasBLift E)
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) (hPE : P.map (QuotientGroup.mk' (oddCore H)) ≤ E) :
    P ≤ centralizer (oddCore H : Set H) :=
  (le_oddCoreLift_of_perfect hP hPE).trans h

theorem oddCoreLift_normal (E : Subgroup (H ⧸ oddCore H)) :
    ((oddCoreLift E).subgroupOf (E.comap (QuotientGroup.mk' (oddCore H)))).Normal :=
  CFSG.Quasithin.perfectCore_normal _

variable [Finite H]

theorem commutator_oddCoreLift (E : Subgroup (H ⧸ oddCore H)) :
    ⁅oddCoreLift E, oddCoreLift E⁆ = oddCoreLift E :=
  perfectCore_perfect _

theorem map_oddCoreLift {E : Subgroup (H ⧸ oddCore H)} (hE : ⁅E, E⁆ = E) :
    (oddCoreLift E).map (QuotientGroup.mk' (oddCore H)) = E := by
  rw [oddCoreLift, CFSG.Quasithin.map_perfectCore,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hE]

theorem comap_eq_oddCoreLift_sup {E : Subgroup (H ⧸ oddCore H)} (hE : ⁅E, E⁆ = E) :
    E.comap (QuotientGroup.mk' (oddCore H)) = oddCoreLift E ⊔ oddCore H := by
  apply le_antisymm
  · intro x hx
    have hx' : QuotientGroup.mk' (oddCore H) x ∈ (oddCoreLift E).map (QuotientGroup.mk' _) :=
      (map_oddCoreLift hE).symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hn : y⁻¹ * x ∈ oddCore H := by
      rw [← QuotientGroup.ker_mk' (oddCore H), MonoidHom.mem_ker, map_mul, map_inv, hyx,
        inv_mul_cancel]
    have := mul_mem (mem_sup_left hy)
      (mem_sup_right hn : y⁻¹ * x ∈ oddCoreLift E ⊔ oddCore H)
    rwa [mul_inv_cancel_left] at this
  · refine sup_le (oddCoreLift_le_comap E) fun x hx => ?_
    rw [mem_comap, show QuotientGroup.mk' (oddCore H) x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem E

omit [Finite H] in
theorem HasBLift.inf_le_center {E : Subgroup (H ⧸ oddCore H)} (h : HasBLift E) :
    (oddCore H).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) := by
  intro x hx
  rw [mem_subgroupOf] at hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact (mem_centralizer_iff.1 (h y.2) x hx).symm

theorem HasBLift.isQuasisimple {E : Subgroup (H ⧸ oddCore H)} (h : HasBLift E)
    (hE : CFSG.IsQuasisimple E) : CFSG.IsQuasisimple (oddCoreLift E) := by
  have hEp : ⁅E, E⁆ = E := isPerfect_iff.mp hE.1
  have hmap := map_oddCoreLift hEp
  let f : oddCoreLift E →* E := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp
    ((QuotientGroup.mk' (oddCore H)).subgroupMap (oddCoreLift E))
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hmap).surjective.comp
      ((QuotientGroup.mk' (oddCore H)).subgroupMap_surjective _)
  have hker : f.ker ≤ center (oddCoreLift E) := by
    intro x hx
    apply h.inf_le_center
    rw [mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact h1
  have hP : Group.IsPerfect (oddCoreLift E) := isPerfect_iff.mpr (commutator_oddCoreLift E)
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hP f hf hker).2 hE

theorem HasBLift.isComponent {E : Subgroup (H ⧸ oddCore H)} (h : HasBLift E)
    (hE : CFSG.IsComponent E) : CFSG.IsComponent (oddCoreLift E) :=
  ⟨h.isQuasisimple hE.1, IsSubnormal.trans (oddCoreLift_le_comap E)
    (oddCoreLift_normal E).isSubnormal (hE.2.comap _)⟩

theorem oddCoreLift_le_commutator {t : H} {E : Subgroup (H ⧸ oddCore H)} (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore H) t ∈ normalizer (E : Set (H ⧸ oddCore H)))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore H) t)⁆) :
    oddCoreLift E ≤ ⁅oddCoreLift E, zpowers t⁆ := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set L := oddCoreLift E with hL
  have hOodd : Odd (Nat.card (oddCore H)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have htL : t ∈ normalizer (L : Set H) := mem_normalizer_oddCoreLift E htE
  have hCL : ⁅L, zpowers t⁆ ≤ L := le_normalizer_iff_commutator_le_left.1 (zpowers_le.2 htL)
  have hle : L ≤ ⁅L, zpowers t⁆ ⊔ (L ⊓ oddCore H) := by
    intro x hx
    have h1 : π x ∈ ⁅L, zpowers t⁆.map π := by
      rw [map_commutator, map_oddCoreLift hE, MonoidHom.map_zpowers]
      exact hEt ((map_oddCoreLift hE) ▸ mem_map_of_mem π hx)
    obtain ⟨y, hy, hyx⟩ := h1
    have hn : y⁻¹ * x ∈ oddCore H := by
      rw [← QuotientGroup.ker_mk' (oddCore H), MonoidHom.mem_ker, map_mul, map_inv, hyx,
        inv_mul_cancel]
    have hnL : y⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hCL hy)) hx
    have := mul_mem (mem_sup_left hy)
      (mem_sup_right ⟨hnL, hn⟩ : y⁻¹ * x ∈ ⁅L, zpowers t⁆ ⊔ (L ⊓ oddCore H))
    rwa [mul_inv_cancel_left] at this
  have hsolv : Group.IsSolvable (L ⊓ oddCore H : Subgroup H) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hOodd.of_dvd_nat (card_dvd_of_le inf_le_right))
  have hLeq : L = ⁅L, zpowers t⁆ ⊔ (L ⊓ oddCore H) := le_antisymm hle (sup_le hCL inf_le_left)
  have hn : (⁅L, zpowers t⁆.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCL).2 (normalizer_commutator_ge_left L (zpowers t))
  have key := CFSG.Quasithin.perfectCore_le_of_sup_solvable hCL hn hLeq hsolv
  rwa [CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_oddCoreLift E)] at key

theorem hasBLift_of_commute {t : H} (ht : t * t = 1) {E : Subgroup (H ⧸ oddCore H)}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore H) t ∈ normalizer (E : Set (H ⧸ oddCore H)))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore H) t)⁆)
    (hC : ∀ c ∈ oddCore H, c * t = t * c → c ∈ centralizer (oddCoreLift E : Set H)) :
    HasBLift E := by
  have hOodd : Odd (Nat.card (oddCore H)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  exact le_centralizer_of_le_closure (N := oddCore H) hOodd ht
    (oddCoreLift_le_commutator hE htE hEt) le_normalizer (mem_normalizer_oddCoreLift E htE) hC
    (le_closure_two_pow_of_perfect (commutator_oddCoreLift E))

theorem hasBLift_of_le_center {t : H} (ht : t * t = 1) {E : Subgroup (H ⧸ oddCore H)}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore H) t ∈ normalizer (E : Set (H ⧸ oddCore H)))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore H) t)⁆)
    (hC : ∀ c ∈ oddCore H, c * t = t * c → c ∈ center H) : HasBLift E :=
  hasBLift_of_commute ht hE htE hEt fun c hc hct =>
    mem_centralizer_iff.2 fun y _ => mem_center_iff.1 (hC c hc hct) y

theorem isComponent_oddCoreLift_of_le_center {t : H} (ht : t * t = 1)
    {E : Subgroup (H ⧸ oddCore H)} (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore H) t ∈ normalizer (E : Set (H ⧸ oddCore H)))
    (htE' : QuotientGroup.mk' (oddCore H) t ∉ centralizer (E : Set (H ⧸ oddCore H)))
    (hC : ∀ c ∈ oddCore H, c * t = t * c → c ∈ center H) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore H)) = E ∧
      (oddCore H).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) := by
  have hEp : ⁅E, E⁆ = E := isPerfect_iff.mp hE.1.1
  have h := hasBLift_of_le_center ht hEp htE
    (le_commutator_zpowers_of_isQuasisimple hE.1 htE htE') hC
  exact ⟨h, h.isComponent hE, map_oddCoreLift hEp, h.inf_le_center⟩

theorem hasBLift_sup_conj_of_le_center {t : H} (ht : t * t = 1) {K : Subgroup (H ⧸ oddCore H)}
    (hK : ⁅K, K⁆ = K)
    (hcomm : ⁅K, K.map (MulAut.conj (QuotientGroup.mk' (oddCore H) t)).toMonoidHom⁆ = ⊥)
    (hC : ∀ c ∈ oddCore H, c * t = t * c → c ∈ center H) :
    HasBLift (K ⊔ K.map (MulAut.conj (QuotientGroup.mk' (oddCore H) t)).toMonoidHom) ∧
      HasBLift K := by
  set τ := QuotientGroup.mk' (oddCore H) t with hτ
  set E := K ⊔ K.map (MulAut.conj τ).toMonoidHom with hEdef
  have hττ : τ * τ = 1 := by rw [hτ, ← map_mul, ht, map_one]
  have hKτ : ⁅K.map (MulAut.conj τ).toMonoidHom, K.map (MulAut.conj τ).toMonoidHom⁆ =
      K.map (MulAut.conj τ).toMonoidHom := by
    rw [← map_commutator, hK]
  have hEp : ⁅E, E⁆ = E :=
    le_antisymm (CFSG.Quasithin.A3.commutator_self_le E) (sup_le
      (hK.symm.le.trans (commutator_mono le_sup_left le_sup_left))
      (hKτ.symm.le.trans (commutator_mono le_sup_right le_sup_right)))
  have hid : (MulAut.conj τ).toMonoidHom.comp (MulAut.conj τ).toMonoidHom =
      MonoidHom.id _ := by
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    calc τ * (τ * y * τ⁻¹) * τ⁻¹ = (τ * τ) * y * (τ * τ)⁻¹ := by group
      _ = y := by rw [hττ]; group
  have hEmap : E.map (MulAut.conj τ).toMonoidHom = E := by
    rw [hEdef, Subgroup.map_sup, map_map, hid, map_id, sup_comm]
  have hτE : τ ∈ normalizer (E : Set (H ⧸ oddCore H)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    exact hEmap
  have h := hasBLift_of_le_center ht hEp hτE (sup_conj_le_commutator_zpowers hK hcomm) hC
  exact ⟨h, h.mono le_sup_left⟩

end Lift

end CFSG.SeitzReduction.F4Pilot

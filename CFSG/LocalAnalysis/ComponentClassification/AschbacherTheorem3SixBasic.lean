module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport2

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

structure Conf46 (G T S Q H : Subgroup X) (g : X) : Prop where
  sylowFrame : SylowFrame G T S
  hyp43 : Hyp43 G T Q H
  mem : g ∈ G
  ne : rightConjugate T g ≠ T
  le_normalizer : rightConjugate T g ≤ Subgroup.normalizer (T : Set X)
  weakClosure : relativeWeakClosure G T S = T ⊔ rightConjugate T g
  pRank_lt : 1 < pRank 2 T

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem frame (c : Conf46 G T S Q H g) : Frame G T := c.sylowFrame.toFrame

theorem le_S (c : Conf46 G T S Q H g) : T ≤ S := c.sylowFrame.le

theorem isPGroup_S (c : Conf46 G T S Q H g) : IsPGroup 2 S := c.sylowFrame.sylow.isPGroup

theorem le_sup (c : Conf46 G T S Q H g) : S ≤ G ⊔ T := c.sylowFrame.sylow.le

theorem ne_bot (c : Conf46 G T S Q H g) : T ≠ ⊥ :=
  fun hT => c.ne (by rw [hT, rightConjugate_bot])

theorem W_le_S (c : Conf46 G T S Q H g) : T ⊔ rightConjugate T g ≤ S :=
  c.weakClosure ▸ relative_weak_closure_le _ _ _

theorem conj_le_H (c : Conf46 G T S Q H g) : rightConjugate T g ≤ H := fun _ hx =>
  c.hyp43.normalizer_le c.frame c.ne_bot
    ⟨c.le_sup (c.W_le_S (Subgroup.mem_sup_right hx)), c.le_normalizer hx⟩

theorem hyp45 (c : Conf46 G T S Q H g) : Hyp45 G T S Q H g where
  sylowFrame := c.sylowFrame
  hyp43 := c.hyp43
  mem := c.mem
  ne := c.ne
  weakClosure := by
    apply le_antisymm
    · rw [← c.weakClosure]
      exact relative_weak_closure_mono _ _ _ _ inf_le_right
    · refine sup_le (subgroup_le_relative_weak_closure _ _ _
        (le_inf c.hyp43.le_H c.le_S)) ?_
      exact rightConjugate_le_relativeWeakClosure c.mem
        (le_inf c.conj_le_H (le_sup_right.trans c.W_le_S))

theorem isMulCommutative (c : Conf46 G T S Q H g) : IsMulCommutative T :=
  c.hyp45.isMulCommutative

theorem isMulCommutative_W (c : Conf46 G T S Q H g) :
    IsMulCommutative (T ⊔ rightConjugate T g : Subgroup X) :=
  c.hyp45.facts.2.2.2

theorem le_normalizer_W (c : Conf46 G T S Q H g) :
    S ≤ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  rw [← c.weakClosure]
  exact le_normalizer_relativeWeakClosure c.frame c.le_sup c.le_S

theorem commutator_mem_G (c : Conf46 G T S Q H g) {s t : X} (hs : s ∈ S) (ht : t ∈ T) :
    s * t * s⁻¹ * t⁻¹ ∈ G := by
  obtain ⟨t₀, ht₀, h₀, hh₀, rfl⟩ := c.frame.mem_sup_iff.mp (c.le_sup hs)
  have hcomm : t₀ * t = t * t₀ := congrArg Subtype.val (c.isMulCommutative.is_comm.comm
    ⟨t₀, ht₀⟩ ⟨t, ht⟩)
  have h1 : t * h₀⁻¹ * t⁻¹ ∈ G :=
    (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer ht) _).mp (G.inv_mem hh₀)
  have h2 : t₀ * (h₀ * (t * h₀⁻¹ * t⁻¹)) * t₀⁻¹ ∈ G :=
    (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer ht₀) _).mp (G.mul_mem hh₀ h1)
  have heq : t₀ * h₀ * t * (t₀ * h₀)⁻¹ * t⁻¹ = t₀ * (h₀ * (t * h₀⁻¹ * t⁻¹)) * t₀⁻¹ := by
    calc t₀ * h₀ * t * (t₀ * h₀)⁻¹ * t⁻¹ = t₀ * (h₀ * t * h₀⁻¹) * (t₀⁻¹ * t⁻¹) := by group
      _ = t₀ * (h₀ * t * h₀⁻¹) * (t⁻¹ * t₀⁻¹) := by
          rw [← mul_inv_rev, ← mul_inv_rev, hcomm]
      _ = t₀ * (h₀ * (t * h₀⁻¹ * t⁻¹)) * t₀⁻¹ := by group
  rw [heq]
  exact h2

theorem commutator_mem (c : Conf46 G T S Q H g) {s t : X} (hs : s ∈ S) (ht : t ∈ T) :
    s * t * s⁻¹ * t⁻¹ ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  refine ⟨?_, c.commutator_mem_G hs ht⟩
  have htW : t ∈ T ⊔ rightConjugate T g := Subgroup.mem_sup_left ht
  have h1 : s * t * s⁻¹ ∈ T ⊔ rightConjugate T g :=
    (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_W hs) t).mp htW
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ htW)

theorem omegaOne_Z_le (c : Conf46 G T S Q H g) :
    omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤
      omegaOne S ⊓ Subgroup.centralizer (omegaOne S : Set X) := by
  have h := lemma_4_5_four c.hyp45
  rwa [inf_eq_left.mpr c.le_normalizer_W] at h

theorem commutator_mem_omegaOne (c : Conf46 G T S Q H g) {s u : X} (hs : s ∈ S)
    (hu : u ∈ omegaOne T) : s * u * s⁻¹ * u⁻¹ ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  have hW := c.isMulCommutative_W
  have hu' := (mem_omegaOne_iff c.isMulCommutative).mp hu
  have hZab : IsMulCommutative ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) :=
    isMulCommutative_of_le inf_le_left hW
  refine (mem_omegaOne_iff hZab).mpr ⟨c.commutator_mem hs hu'.1, ?_⟩
  have huW : u ∈ T ⊔ rightConjugate T g := Subgroup.mem_sup_left hu'.1
  have hsu : s * u * s⁻¹ ∈ T ⊔ rightConjugate T g :=
    (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_W hs) u).mp huW
  have hcomm : s * u * s⁻¹ * u⁻¹ = u⁻¹ * (s * u * s⁻¹) :=
    congrArg Subtype.val (hW.is_comm.comm ⟨_, hsu⟩ ⟨_, Subgroup.inv_mem _ huW⟩)
  have hsu2 : (s * u * s⁻¹) ^ 2 = 1 := by
    rw [pow_two, show s * u * s⁻¹ * (s * u * s⁻¹) = s * (u * u) * s⁻¹ by group, ← pow_two,
      hu'.2, mul_one, mul_inv_cancel]
  have hu2 : u⁻¹ ^ 2 = 1 := by rw [inv_pow, hu'.2, inv_one]
  rw [pow_two]
  calc s * u * s⁻¹ * u⁻¹ * (s * u * s⁻¹ * u⁻¹)
      = s * u * s⁻¹ * u⁻¹ * (u⁻¹ * (s * u * s⁻¹)) := by rw [← hcomm]
    _ = s * u * s⁻¹ * (u⁻¹ ^ 2) * (s * u * s⁻¹) := by rw [pow_two]; group
    _ = (s * u * s⁻¹) ^ 2 := by rw [hu2, mul_one, pow_two]
    _ = 1 := hsu2

theorem omegaOne_W (c : Conf46 G T S Q H g) :
    omegaOne (T ⊔ rightConjugate T g) =
      omegaOne T ⊔ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  set W := T ⊔ rightConjugate T g with hWdef
  set Z := W ⊓ G with hZdef
  have hW := c.isMulCommutative_W
  obtain ⟨hdec, hinf⟩ := c.hyp45.W_decomp
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hx2⟩ := (mem_omegaOne_iff hW).mp hx
    have hTZ : T ≤ Subgroup.normalizer (Z : Set X) := fun t ht =>
      Subgroup.mem_normalizer_iff.mpr fun z => by
        constructor
        · intro hz
          have h1 : t * z = z * t := congrArg Subtype.val
            (hW.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩ ⟨z, hz.1⟩)
          rw [h1, mul_inv_cancel_right]
          exact hz
        · intro hz
          have hzW : z ∈ W := by
            have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
              (Subgroup.mem_sup_left ht : t ∈ W)) hz.1) (Subgroup.mem_sup_left ht : t ∈ W)
            simpa [mul_assoc] using this
          have h1 : t * z = z * t := congrArg Subtype.val
            (hW.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩ ⟨z, hzW⟩)
          have h2 : t * z * t⁻¹ = z := by rw [h1, mul_inv_cancel_right]
          rw [h2] at hz
          exact hz
    have hxm : x ∈ (T : Set X) * (Z : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T Z hTZ]
      rw [hdec] at hxW
      exact hxW
    obtain ⟨t, ht, z, hz, rfl⟩ := Set.mem_mul.mp hxm
    have htz : t * z = z * t := congrArg Subtype.val
      (hW.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩ ⟨z, hz.1⟩)
    have hsq : t ^ 2 * z ^ 2 = 1 := by
      rw [← hx2, pow_two, pow_two, pow_two]
      calc t * t * (z * z) = t * (t * z) * z := by group
        _ = t * (z * t) * z := by rw [htz]
        _ = t * z * (t * z) := by group
    have ht2 : t ^ 2 ∈ T ⊓ Z := by
      refine ⟨T.pow_mem ht 2, ?_⟩
      have : t ^ 2 = (z ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact Z.inv_mem (Z.pow_mem hz 2)
    rw [hinf, Subgroup.mem_bot] at ht2
    have hz2 : z ^ 2 = 1 := by rw [ht2, one_mul] at hsq; exact hsq
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_omegaOne ht ht2))
      (Subgroup.mem_sup_right (mem_omegaOne hz hz2))
  · exact sup_le (omegaOne_mono le_sup_left) (omegaOne_mono inf_le_left)

theorem omegaOne_W_inf (c : Conf46 G T S Q H g) :
    omegaOne (T ⊔ rightConjugate T g) ⊓ G = omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  have hW := c.isMulCommutative_W
  have hZ : IsMulCommutative ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) :=
    isMulCommutative_of_le inf_le_left hW
  apply le_antisymm
  · rintro x ⟨hx, hxG⟩
    obtain ⟨hxW, hx2⟩ := (mem_omegaOne_iff hW).mp hx
    exact mem_omegaOne ⟨hxW, hxG⟩ hx2
  · exact le_inf (omegaOne_mono inf_le_left) ((omegaOne_le _).trans inf_le_right)

theorem weakClosure_omegaOne (c : Conf46 G T S Q H g) :
    relativeWeakClosure G (omegaOne T) S = omegaOne (T ⊔ rightConjugate T g) :=
  lemma_4_5_five_weakClosure c.hyp45 c.pRank_lt c.weakClosure

theorem omegaOne_ne_bot (c : Conf46 G T S Q H g) : omegaOne T ≠ ⊥ := by
  obtain ⟨z, hzT, hz2, -⟩ := exists_center_involution c.frame.isPGroup c.ne_bot
  intro hbot
  have hz : z ∈ omegaOne T := mem_omegaOne hzT (by rw [← hz2, pow_orderOf_eq_one])
  rw [hbot, Subgroup.mem_bot] at hz
  rw [hz, orderOf_one] at hz2
  omega

theorem normalizer_omegaOne_le (c : Conf46 G T S Q H g) :
    (G ⊔ T) ⊓ Subgroup.normalizer (omegaOne T : Set X) ≤ H := by
  rintro x ⟨hx, hxN⟩
  apply c.hyp43.mem_of_inf_ne_bot_sup c.frame hx
  intro hbot
  apply c.omegaOne_ne_bot
  rw [eq_bot_iff, ← hbot]
  refine le_inf (omegaOne_le T) ?_
  have h := rightConjugate_le_rightConjugate (omegaOne_le T) x
  rwa [(rightConjugate_eq_self_iff _ x).mpr hxN] at h

theorem conj_omegaOne_eq (c : Conf46 G T S Q H g) {m : X} (hm : m ∈ G)
    (hmN : m ∈ Subgroup.normalizer (omegaOne T : Set X))
    (hle : rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) m ≤ S) :
    rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) m =
      omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G)
  set U := omegaOne T
  have hUm : rightConjugate U m = U := (rightConjugate_eq_self_iff _ m).mpr hmN
  have hVm : rightConjugate V m ≤ S := by
    rw [hVdef, c.omegaOne_W]
    unfold rightConjugate
    rw [Subgroup.map_sup]
    refine sup_le ?_ hle
    change rightConjugate U m ≤ S
    rw [hUm]
    exact (omegaOne_le T).trans c.le_S
  have hVV : rightConjugate V m ≤ V := by
    have hWU : relativeWeakClosure G U S = V := c.weakClosure_omegaOne
    have hVle : V ≤ rightConjugate V m⁻¹ := by
      have hgoal : relativeWeakClosure G U S ≤ rightConjugate V m⁻¹ := by
        rw [relativeWeakClosure_le_iff]
        intro x hx hxS
        have h1 : rightConjugate U x ≤ V := by
          rw [← hWU]
          exact rightConjugate_le_relativeWeakClosure hx hxS
        have h2 : rightConjugate (rightConjugate U x) m ≤ rightConjugate V m :=
          rightConjugate_le_rightConjugate h1 m
        rw [rightConjugate_mul] at h2
        have h3 : rightConjugate U (x * m) ≤ V := by
          rw [← hWU]
          exact rightConjugate_le_relativeWeakClosure (G.mul_mem hx hm) (h2.trans hVm)
        have h4 := rightConjugate_le_rightConjugate h3 m⁻¹
        rwa [rightConjugate_mul, mul_inv_cancel_right] at h4
      rwa [hWU] at hgoal
    have h := rightConjugate_le_rightConjugate hVle m
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h
  have hVeq : rightConjugate V m = V :=
    Subgroup.eq_of_le_of_card_ge hVV (by rw [rightConjugate_card])
  have hZ1 : Z₁ = V ⊓ G := c.omegaOne_W_inf.symm
  rw [hZ1, rightConjugate_inf, hVeq, rightConjugate_eq_of_mem hm]

theorem omegaOne_W_eq_conj (c : Conf46 G T S Q H g) :
    omegaOne (T ⊔ rightConjugate T g) = omegaOne T ⊔ rightConjugate (omegaOne T) g := by
  set W := T ⊔ rightConjugate T g with hWdef
  set K := rightConjugate T g with hK
  have hW := c.isMulCommutative_W
  have hinf : T ⊓ K = ⊥ := c.hyp45.facts.2.1
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hx2⟩ := (mem_omegaOne_iff hW).mp hx
    have hxm : x ∈ (T : Set X) * (K : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left T K c.le_normalizer]
      exact hxW
    obtain ⟨t, ht, k, hk, rfl⟩ := Set.mem_mul.mp hxm
    have htk : t * k = k * t := congrArg Subtype.val
      (hW.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩ ⟨k, Subgroup.mem_sup_right hk⟩)
    have hsq : t ^ 2 * k ^ 2 = 1 := by
      rw [← hx2, pow_two, pow_two, pow_two]
      calc t * t * (k * k) = t * (t * k) * k := by group
        _ = t * (k * t) * k := by rw [htk]
        _ = t * k * (t * k) := by group
    have ht2 : t ^ 2 ∈ T ⊓ K := by
      refine ⟨T.pow_mem ht 2, ?_⟩
      have : t ^ 2 = (k ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact K.inv_mem (K.pow_mem hk 2)
    rw [hinf, Subgroup.mem_bot] at ht2
    have hk2 : k ^ 2 = 1 := by rw [ht2, one_mul] at hsq; exact hsq
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_omegaOne ht ht2))
      (Subgroup.mem_sup_right ?_)
    rw [rightConjugate_omegaOne]
    exact mem_omegaOne hk hk2
  · refine sup_le (omegaOne_mono le_sup_left) ?_
    rw [rightConjugate_omegaOne]
    exact omegaOne_mono le_sup_right

theorem card_omegaOne_W (c : Conf46 G T S Q H g) :
    Nat.card (omegaOne (T ⊔ rightConjugate T g)) =
      Nat.card (omegaOne T) * Nat.card (omegaOne T) := by
  have hinf : omegaOne T ⊓ rightConjugate (omegaOne T) g = ⊥ := by
    rw [eq_bot_iff, ← c.hyp45.facts.2.1]
    exact inf_le_inf (omegaOne_le T) (rightConjugate_le_rightConjugate (omegaOne_le T) g)
  have hN : rightConjugate (omegaOne T) g ≤ Subgroup.normalizer (omegaOne T : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    have hxW : x ∈ T ⊔ rightConjugate T g :=
      Subgroup.mem_sup_right (rightConjugate_le_rightConjugate (omegaOne_le T) g hx)
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => congrArg Subtype.val
      (c.isMulCommutative_W.is_comm.comm ⟨u, Subgroup.mem_sup_left (omegaOne_le T hu)⟩ ⟨x, hxW⟩)
  rw [c.omegaOne_W_eq_conj, card_sup_of_le_normalizer hN hinf, rightConjugate_card]

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3

module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux2

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsShortGroup)
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Case4 (K T P S W : Subgroup G) (x : G) : Prop where
  blk : QBlock K
  tnorm : T ≤ Subgroup.normalizer (K : Set G)
  tinf : T ⊓ K = ⊥
  sylowP : IsSylowOf 2 T P
  ple : P ≤ K ⊔ T
  tight : TightlyEmbedded (P.subgroupOf (K ⊔ T))
  sylowS : IsSylowOf 2 S (K ⊔ T)
  sylowN : IsSylowOf 2 (S ⊓ Subgroup.normalizer (T : Set G))
    ((K ⊔ T) ⊓ Subgroup.normalizer (T : Set G))
  hx : x ∈ K
  hWdef : W = T ⊔ rightConjugate T x
  hTx : T ⊓ rightConjugate T x = ⊥
  hcomm : ∀ a ∈ T, ∀ b ∈ rightConjugate T x, a * b = b * a
  hWN : W = S ⊓ Subgroup.normalizer (T : Set G)
  hWnorm : K ⊔ T ≤ Subgroup.normalizer (W : Set G)
  hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a

@[expose] def dl (g w : G) : G := w⁻¹ * (g⁻¹ * w * g)

omit [Finite G] in
theorem dl_eq_commutator (g w : G) : dl g w = ⁅w⁻¹, g⁻¹⁆ := by
  unfold dl
  rw [commutatorElement_def]
  group

omit [Finite G] in
theorem dl_one_right (g : G) : dl g 1 = 1 := by simp [dl]

omit [Finite G] in
theorem dl_eq_one_iff {g w : G} : dl g w = 1 ↔ w * g = g * w := by
  unfold dl
  constructor
  · intro h
    have : g⁻¹ * w * g = w := by
      have := congrArg (fun z => w * z) h
      simpa [← mul_assoc] using this
    calc w * g = g * (g⁻¹ * w * g) := by group
      _ = g * w := by rw [this]
  · intro h
    calc w⁻¹ * (g⁻¹ * w * g) = w⁻¹ * (g⁻¹ * (w * g)) := by group
      _ = w⁻¹ * (g⁻¹ * (g * w)) := by rw [h]
      _ = 1 := by group

namespace Case4

variable {K T P S W : Subgroup G} {x : G} (c : Case4 K T P S W x)

include c

theorem tIsPGroup : IsPGroup 2 T := c.sylowP.isPGroup

theorem W_le_S : W ≤ S := by
  rw [c.hWN]
  exact inf_le_left

theorem W_isPGroup : IsPGroup 2 W := c.sylowS.isPGroup.to_le c.W_le_S

theorem T_le_W : T ≤ W := by
  rw [c.hWdef]
  exact le_sup_left

theorem W_le_KT : W ≤ K ⊔ T := c.W_le_S.trans c.sylowS.le

theorem KT_norm_K : K ⊔ T ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer c.tnorm

theorem K_norm_W : K ≤ Subgroup.normalizer (W : Set G) := fun _ hg =>
  c.hWnorm (Subgroup.mem_sup_left hg)

theorem Tx_comm : ∀ a ∈ rightConjugate T x, ∀ b ∈ rightConjugate T x, a * b = b * a := by
  intro a ha b hb
  rw [mem_rightConjugate_iff] at ha hb
  have h := c.hTab _ ha _ hb
  have h2 : x * (a * b) * x⁻¹ = x * (b * a) * x⁻¹ := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = (x * b * x⁻¹) * (x * a * x⁻¹) := h
      _ = x * (b * a) * x⁻¹ := by group
  have h3 := congrArg (fun z => x⁻¹ * z * x) h2
  simpa [mul_assoc] using h3

theorem mem_W_iff (z : G) : z ∈ W ↔ ∃ a ∈ T, ∃ b ∈ rightConjugate T x, z = a * b := by
  rw [c.hWdef]
  exact mem_sup_iff_of_commute c.hcomm

theorem W_comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a1, ha1, a2, ha2, rfl⟩ := (c.mem_W_iff a).1 ha
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ := (c.mem_W_iff b).1 hb
  have h1 := c.hTab a1 ha1 b1 hb1
  have h2 := c.Tx_comm a2 ha2 b2 hb2
  have h3 := c.hcomm a1 ha1 b2 hb2
  have h4 := c.hcomm b1 hb1 a2 ha2
  calc a1 * a2 * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
    _ = a1 * (b1 * a2) * b2 := by rw [← h4]
    _ = (a1 * b1) * (a2 * b2) := by group
    _ = (b1 * a1) * (b2 * a2) := by rw [h1, h2]
    _ = b1 * (a1 * b2) * a2 := by group
    _ = b1 * (b2 * a1) * a2 := by rw [h3]
    _ = b1 * b2 * (a1 * a2) := by group

theorem comm_le : ⁅W, K⁆ ≤ W ⊓ K := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have hwKT : w ∈ K ⊔ T := c.W_le_KT hw
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : k * w⁻¹ * k⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (c.K_norm_W hk) w⁻¹).1 (W.inv_mem hw)
    have : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact W.mul_mem hw h1
  · have h1 : w * k * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (c.KT_norm_K hwKT) k).1 hk
    rw [commutatorElement_def]
    exact K.mul_mem h1 (K.inv_mem hk)

theorem inf_le_oTwo : W ⊓ K ≤ oTwoIn K := by
  refine SixThree.le_oTwoIn_of_isPGroup inf_le_right (c.W_isPGroup.to_le inf_le_left) ?_
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hW := Subgroup.mem_normalizer_iff.1 (c.K_norm_W hk) y
  have hK := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hk : k ∈ Subgroup.normalizer
    (K : Set G)) y
  exact ⟨fun hy => ⟨hW.1 hy.1, hK.1 hy.2⟩, fun hy => ⟨hW.2 hy.1, hK.2 hy.2⟩⟩

theorem comm_eq_blockU (hne : ⁅T, K⁆ ≠ ⊥) : ⁅W, K⁆ = blockU K := by
  have hne' : ⁅W, K⁆ ≠ ⊥ := fun h => hne (le_bot_iff.1
    ((Subgroup.commutator_mono c.T_le_W le_rfl).trans h.le))
  exact SixThree.commutator_eq_U c.blk.short c.W_isPGroup c.K_norm_W
    (c.comm_le.trans c.inf_le_oTwo) hne'

theorem blockU_le_inf (hne : ⁅T, K⁆ ≠ ⊥) : blockU K ≤ W ⊓ K := by
  rw [← c.comm_eq_blockU hne]
  exact c.comm_le

theorem dl_mem_blockU (hne : ⁅T, K⁆ ≠ ⊥) {g w : G} (hg : g ∈ K) (hw : w ∈ W) :
    dl g w ∈ blockU K := by
  rw [dl_eq_commutator, ← c.comm_eq_blockU hne]
  exact Subgroup.commutator_mem_commutator (W.inv_mem hw) (K.inv_mem hg)

theorem exists_dl_eq (hne : ⁅T, K⁆ ≠ ⊥) {w : G} (hw : w ∈ W ⊓ K) :
    ∃ t' ∈ T, w = dl x t' := by
  obtain ⟨hwW, hwK⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨t, ht, s, hs, rfl⟩ := (c.mem_W_iff w).1 hwW
  rw [mem_rightConjugate_iff] at hs
  set t' := x * s * x⁻¹ with ht'def
  have hs' : s = x⁻¹ * t' * x := by
    rw [ht'def]
    group
  have hc : dl x t' ∈ blockU K := c.dl_mem_blockU hne c.hx (c.T_le_W hs)
  have hcK : dl x t' ∈ K := blockU_le K hc
  have hw' : t * s = (t * t') * dl x t' := by
    rw [hs']
    unfold dl
    group
  have htt' : t * t' = (t * s) * (dl x t')⁻¹ := by
    rw [hw']
    group
  have hmem : t * t' ∈ T ⊓ K :=
    ⟨T.mul_mem ht hs, by rw [htt']; exact K.mul_mem hwK (K.inv_mem hcK)⟩
  rw [c.tinf, Subgroup.mem_bot] at hmem
  exact ⟨t', hs, by rw [hw', hmem, one_mul]⟩

theorem inf_le_blockU (hne : ⁅T, K⁆ ≠ ⊥) : W ⊓ K ≤ blockU K := by
  intro w hw
  obtain ⟨t', ht', rfl⟩ := c.exists_dl_eq hne hw
  exact c.dl_mem_blockU hne c.hx (c.T_le_W ht')

theorem inf_eq_blockU (hne : ⁅T, K⁆ ≠ ⊥) : W ⊓ K = blockU K :=
  le_antisymm (c.inf_le_blockU hne) (c.blockU_le_inf hne)

theorem blockU_le_W (hne : ⁅T, K⁆ ≠ ⊥) : blockU K ≤ W := (c.blockU_le_inf hne).trans inf_le_left

theorem dl_mem_W {g w : G} (hg : g ∈ K) (hw : w ∈ W) : dl g w ∈ W := by
  unfold dl
  have h1 : g⁻¹ * w * g⁻¹⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.1 (c.K_norm_W (K.inv_mem hg)) w).1 hw
  rw [inv_inv] at h1
  exact W.mul_mem (W.inv_mem hw) h1

theorem dl_mul_W {g w₁ w₂ : G} (hg : g ∈ K) (h₁ : w₁ ∈ W) (h₂ : w₂ ∈ W) :
    dl g (w₁ * w₂) = dl g w₁ * dl g w₂ := by
  have hd := c.dl_mem_W hg h₁
  have hcomm : w₂⁻¹ * dl g w₁ = dl g w₁ * w₂⁻¹ := c.W_comm _ (W.inv_mem h₂) _ hd
  unfold dl at hcomm ⊢
  calc (w₁ * w₂)⁻¹ * (g⁻¹ * (w₁ * w₂) * g)
      = w₂⁻¹ * (w₁⁻¹ * (g⁻¹ * w₁ * g)) * (g⁻¹ * w₂ * g) := by group
    _ = (w₁⁻¹ * (g⁻¹ * w₁ * g)) * w₂⁻¹ * (g⁻¹ * w₂ * g) := by rw [hcomm]
    _ = w₁⁻¹ * (g⁻¹ * w₁ * g) * (w₂⁻¹ * (g⁻¹ * w₂ * g)) := by group

theorem dl_inv_W {g w : G} (hg : g ∈ K) (hw : w ∈ W) : dl g w⁻¹ = (dl g w)⁻¹ := by
  have h := c.dl_mul_W hg (W.inv_mem hw) hw
  rw [inv_mul_cancel, dl_one_right] at h
  exact eq_inv_of_mul_eq_one_left h.symm

omit [Finite G] c in
theorem mem_inf_of_dl_eq_one {g t : G} (ht : t ∈ T) (h : dl g t = 1) :
    t ∈ T ⊓ rightConjugate T g := by
  refine Subgroup.mem_inf.2 ⟨ht, ?_⟩
  rw [mem_rightConjugate_iff]
  have h1 : t * g = g * t := dl_eq_one_iff.1 h
  have : g * t * g⁻¹ = t := by
    calc g * t * g⁻¹ = (t * g) * g⁻¹ := by rw [h1]
      _ = t := by group
  rw [this]
  exact ht

theorem dl_injOn {g : G} (hg : g ∈ K) (hTg : T ⊓ rightConjugate T g = ⊥) :
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, dl g t₁ = dl g t₂ → t₁ = t₂ := by
  intro t₁ h₁ t₂ h₂ h
  have h1 : dl g (t₁ * t₂⁻¹) = 1 := by
    rw [c.dl_mul_W hg (c.T_le_W h₁) (W.inv_mem (c.T_le_W h₂)),
      c.dl_inv_W hg (c.T_le_W h₂), h]
    simp
  have h2 := mem_inf_of_dl_eq_one (T.mul_mem h₁ (T.inv_mem h₂)) h1
  rw [hTg, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.1 h2

theorem dl_T_bijective (hne : ⁅T, K⁆ ≠ ⊥) :
    Function.Bijective (fun t : ↥T =>
      (⟨dl x t, c.dl_mem_blockU hne c.hx (c.T_le_W t.2)⟩ : ↥(blockU K))) := by
  constructor
  · intro t₁ t₂ h
    exact Subtype.ext (c.dl_injOn c.hx c.hTx t₁ t₁.2 t₂ t₂.2 (congrArg Subtype.val h))
  · intro u
    obtain ⟨t', ht', hu⟩ := c.exists_dl_eq hne (c.blockU_le_inf hne u.2)
    exact ⟨⟨t', ht'⟩, Subtype.ext hu.symm⟩

theorem card_T_eq (hne : ⁅T, K⁆ ≠ ⊥) : Nat.card ↥T = Nat.card ↥(blockU K) :=
  Nat.card_congr (Equiv.ofBijective _ (c.dl_T_bijective hne))

theorem T_sq (hne : ⁅T, K⁆ ≠ ⊥) : ∀ t ∈ T, t * t = 1 := by
  intro t ht
  have h1 : dl x (t * t) = 1 := by
    rw [c.dl_mul_W c.hx (c.T_le_W ht) (c.T_le_W ht)]
    exact c.blk.blockU_sq_eq_one _ (c.dl_mem_blockU hne c.hx (c.T_le_W ht))
  have h2 := mem_inf_of_dl_eq_one (T.mul_mem ht ht) h1
  rw [c.hTx, Subgroup.mem_bot] at h2
  exact h2

theorem W_sq (hne : ⁅T, K⁆ ≠ ⊥) : ∀ w ∈ W, w * w = 1 := by
  intro w hw
  obtain ⟨t, ht, s, hs, rfl⟩ := (c.mem_W_iff w).1 hw
  have hts : t * s = s * t := c.hcomm t ht s hs
  rw [mem_rightConjugate_iff] at hs
  have hss : s * s = 1 := by
    have h1 := c.T_sq hne _ hs
    calc s * s = x⁻¹ * ((x * s * x⁻¹) * (x * s * x⁻¹)) * x := by group
      _ = 1 := by rw [h1]; group
  calc t * s * (t * s) = t * (s * t) * s := by group
    _ = t * (t * s) * s := by rw [← hts]
    _ = (t * t) * (s * s) := by group
    _ = 1 := by rw [c.T_sq hne t ht, hss]; simp

theorem blockU_le_centralizer_W (hne : ⁅T, K⁆ ≠ ⊥) :
    blockU K ≤ Subgroup.centralizer (W : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact c.W_comm w hw u (c.blockU_le_W hne hu)

theorem blockU_le_centralizer_T (hne : ⁅T, K⁆ ≠ ⊥) :
    blockU K ≤ Subgroup.centralizer (T : Set G) := fun _ hu =>
  (Subgroup.centralizer_le c.T_le_W) (c.blockU_le_centralizer_W hne hu)

omit c [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {N : Subgroup G} {g y : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) (hy : y ∈ Subgroup.centralizer (N : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht0 : g⁻¹ * t * g ∈ N := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (N : Set G)).inv_mem hg) t).1 ht
    simpa using this
  have h := Subgroup.mem_centralizer_iff.1 hy _ ht0
  calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
    _ = g * y * g⁻¹ * t := by group

theorem sylow_blockU (hne : ⁅T, K⁆ ≠ ⊥) :
    IsSylowOf 2 (blockU K) (K ⊓ Subgroup.centralizer (T : Set G)) := by
  have hW : IsSylowOf 2 W ((K ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) := by
    have := c.sylowN
    rwa [← c.hWN] at this
  have hCK : K ⊓ Subgroup.centralizer (T : Set G) ≤ (K ⊔ T) ⊓ Subgroup.normalizer (T : Set G) :=
    fun y hy => Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (Subgroup.mem_inf.1 hy).1,
      Subgroup.centralizer_le_normalizer (T : Set G) (Subgroup.mem_inf.1 hy).2⟩
  have hN : (K ⊔ T) ⊓ Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hK := Subgroup.mem_normalizer_iff.1 (c.KT_norm_K hg.1) y
    constructor
    · intro hy
      exact ⟨(hK.1 hy.1), conj_mem_centralizer_of_mem_normalizer hg.2 hy.2⟩
    · intro hy
      refine ⟨hK.2 hy.1, ?_⟩
      have h1 := conj_mem_centralizer_of_mem_normalizer
        ((Subgroup.normalizer (T : Set G)).inv_mem hg.2) hy.2
      simpa [mul_assoc] using h1
  have hS := IsSylowOf.inf_of_le_normalizer hW hCK hN
  have hEq : W ⊓ (K ⊓ Subgroup.centralizer (T : Set G)) = blockU K := by
    refine le_antisymm ?_ ?_
    · rw [← inf_assoc, c.inf_eq_blockU hne]
      exact inf_le_left
    · exact le_inf (c.blockU_le_W hne) (le_inf (blockU_le K) (c.blockU_le_centralizer_T hne))
  rwa [hEq] at hS

end Case4

end CFSG.CGT.PushingUpLit.LIT.Foote

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Fstar

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

section Toolkit

variable {G : Type} [Group G]

@[expose] def commSub (P N : Subgroup G) (hN : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n) (g : G) :
    Subgroup G where
  carrier := {h | h ∈ P ∧ ⁅g, h⁆ ∈ N}
  one_mem' := ⟨P.one_mem, by simp [N.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, ?_⟩
    have e : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    have : a * ⁅g, b⁆ * a⁻¹ = ⁅g, b⁆ := by
      calc a * ⁅g, b⁆ * a⁻¹ = (⁅g, b⁆ * a) * a⁻¹ := by rw [← hN _ hb a haP]
        _ = ⁅g, b⁆ := by group
    rw [this]
    exact N.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, ?_⟩
    have e : ⁅g, a⁻¹⁆ = a⁻¹ * ⁅g, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅g, a⁆⁻¹ ∈ N := N.inv_mem ha
    have : a⁻¹ * ⁅g, a⁆⁻¹ * a = ⁅g, a⁆⁻¹ := by
      calc a⁻¹ * ⁅g, a⁆⁻¹ * a = a⁻¹ * (⁅g, a⁆⁻¹ * a) := by group
        _ = a⁻¹ * (a * ⁅g, a⁆⁻¹) := by rw [hN _ h1 a haP]
        _ = ⁅g, a⁆⁻¹ := by group
    rw [this]
    exact h1

theorem mem_commSub {P N : Subgroup G} {hN : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n} {g h : G} :
    h ∈ commSub P N hN g ↔ h ∈ P ∧ ⁅g, h⁆ ∈ N := Iff.rfl

theorem commutatorElement_mem_comm {N : Subgroup G} {a b : G} :
    ⁅a, b⁆ ∈ N ↔ ⁅b, a⁆ ∈ N := by
  have : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := (commutatorElement_inv a b).symm
  rw [this, N.inv_mem_iff]

theorem isElemAbelian_sup_of_commute {X Y : Subgroup G} (hX : IsElemAbelian 2 X)
    (hY : IsElemAbelian 2 Y) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    IsElemAbelian 2 (X ⊔ Y) := CFSG.Open.IsElemAbelian.sup_of_commute hX hY hXY

theorem isElemAbelian_conjR {X : Subgroup G} (hX : IsElemAbelian 2 X) (g : G) :
    IsElemAbelian 2 (conjR X g) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    have ha := mem_conjR.mp a.2
    have hb := mem_conjR.mp b.2
    have h := elemAbelian_comm hX ha hb
    have : g * ((a : G) * b) * g⁻¹ = g * ((b : G) * a) * g⁻¹ := by
      calc g * ((a : G) * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
        _ = g * ((b : G) * a) * g⁻¹ := by group
    simpa using this
  · have ha' := mem_conjR.mp ha
    have h := hX.2 _ ha'
    have h' : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by rw [← pow_two]; exact h
    have h2 : g * (a * a) * g⁻¹ = 1 := by
      calc g * (a * a) * g⁻¹ = (g * a * g⁻¹) * (g * a * g⁻¹) := by group
        _ = 1 := h'
    have h3 : a * a = 1 := by simpa using h2
    rw [pow_two]; exact h3

end Toolkit

section Generators

variable {G : Type} [Group G]

@[expose] def sqSub (P N : Subgroup G) (hcomm : ∀ g ∈ P, ∀ h ∈ P, ⁅g, h⁆ ∈ N) : Subgroup G where
  carrier := {g | g ∈ P ∧ g ^ 2 ∈ N}
  one_mem' := ⟨P.one_mem, by simp [N.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, ?_⟩
    have hc : ⁅a⁻¹, b⁆ ∈ N := hcomm _ (P.inv_mem haP) _ hbP
    have e : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
      simp only [commutatorElement_def, pow_two]; group
    rw [e]
    exact N.mul_mem (N.mul_mem ha hc) hb
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, ?_⟩
    have : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by rw [inv_pow]
    rw [this]
    exact N.inv_mem ha

theorem commutators_mem_of_generators {P N A B C : Subgroup G}
    (hN : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n) (hP : P = A ⊔ B ⊔ C)
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ N) (hBcomm : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ N)
    (hCcomm : ∀ c ∈ C, ∀ c' ∈ C, ⁅c, c'⁆ ∈ N)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) (hAC : ∀ a ∈ A, ∀ c ∈ C, ⁅a, c⁆ ∈ N)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, ⁅b, c⁆ ∈ N) :
    ∀ g ∈ P, ∀ h ∈ P, ⁅g, h⁆ ∈ N := by
  have hAP : A ≤ P := hP ▸ (le_sup_left.trans le_sup_left)
  have hBP : B ≤ P := hP ▸ (le_sup_right.trans le_sup_left)
  have hCP : C ≤ P := hP ▸ le_sup_right
  have key : ∀ g : G, A ≤ commSub P N hN g → B ≤ commSub P N hN g → C ≤ commSub P N hN g →
      ∀ h ∈ P, ⁅g, h⁆ ∈ N := by
    intro g hA' hB' hC' h hh
    have : P ≤ commSub P N hN g := hP.le.trans (sup_le (sup_le hA' hB') hC')
    exact (mem_commSub.mp (this hh)).2
  have step1A : ∀ a ∈ A, ∀ h ∈ P, ⁅a, h⁆ ∈ N := fun a ha => key a
    (fun a' ha' => ⟨hAP ha', hAcomm a ha a' ha'⟩)
    (fun b hb => ⟨hBP hb, hAB a ha b hb⟩)
    (fun c hc => ⟨hCP hc, hAC a ha c hc⟩)
  have step1B : ∀ b ∈ B, ∀ h ∈ P, ⁅b, h⁆ ∈ N := fun b hb => key b
    (fun a ha => ⟨hAP ha, commutatorElement_mem_comm.mp (hAB a ha b hb)⟩)
    (fun b' hb' => ⟨hBP hb', hBcomm b hb b' hb'⟩)
    (fun c hc => ⟨hCP hc, hBC b hb c hc⟩)
  have step1C : ∀ c ∈ C, ∀ h ∈ P, ⁅c, h⁆ ∈ N := fun c hc => key c
    (fun a ha => ⟨hAP ha, commutatorElement_mem_comm.mp (hAC a ha c hc)⟩)
    (fun b hb => ⟨hBP hb, commutatorElement_mem_comm.mp (hBC b hb c hc)⟩)
    (fun c' hc' => ⟨hCP hc', hCcomm c hc c' hc'⟩)
  intro g hg h hh
  have : P ≤ commSub P N hN h := hP.le.trans (sup_le (sup_le
    (fun a ha => ⟨hAP ha, commutatorElement_mem_comm.mp (step1A a ha h hh)⟩)
    (fun b hb => ⟨hBP hb, commutatorElement_mem_comm.mp (step1B b hb h hh)⟩))
    (fun c hc => ⟨hCP hc, commutatorElement_mem_comm.mp (step1C c hc h hh)⟩))
  exact commutatorElement_mem_comm.mp (mem_commSub.mp (this hg)).2

theorem sq_mem_of_generators {P N A B C : Subgroup G} (hP : P = A ⊔ B ⊔ C)
    (hcomm : ∀ g ∈ P, ∀ h ∈ P, ⁅g, h⁆ ∈ N)
    (hA : ∀ a ∈ A, a ^ 2 ∈ N) (hB : ∀ b ∈ B, b ^ 2 ∈ N) (hC : ∀ c ∈ C, c ^ 2 ∈ N) :
    ∀ g ∈ P, g ^ 2 ∈ N := by
  have hAP : A ≤ P := hP ▸ (le_sup_left.trans le_sup_left)
  have hBP : B ≤ P := hP ▸ (le_sup_right.trans le_sup_left)
  have hCP : C ≤ P := hP ▸ le_sup_right
  have : P ≤ sqSub P N hcomm := hP.le.trans (sup_le (sup_le
    (fun a ha => ⟨hAP ha, hA a ha⟩) (fun b hb => ⟨hBP hb, hB b hb⟩))
    (fun c hc => ⟨hCP hc, hC c hc⟩))
  exact fun g hg => (this hg).2

theorem frattini_le_of_generators [Finite G] {P N : Subgroup G}
    (hN : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n)
    (hcomm : ∀ g ∈ P, ∀ h ∈ P, ⁅g, h⁆ ∈ N) (hsq : ∀ g ∈ P, g ^ 2 ∈ N) :
    frattiniOf P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      have := hN (n : G) hn g g.2
      calc (g : G) * n * (g : G)⁻¹ = (n * g) * (g : G)⁻¹ := by rw [this]
        _ = n := by group
    show ((g * n * g⁻¹ : P) : G) ∈ N
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
    exact hn⟩
  have h1 : frattini ↥P ≤ N.subgroupOf P :=
    CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 2) (N.subgroupOf P)
      (fun a b => by
        rw [Subgroup.mem_subgroupOf]
        have e : ((⁅a, b⁆ : P) : G) = ⁅(a : G), (b : G)⁆ := map_commutatorElement P.subtype a b
        rw [e]
        exact hcomm a a.2 b b.2)
      (fun a => by
        rw [Subgroup.mem_subgroupOf]
        have e : ((a ^ 2 : P) : G) = (a : G) ^ 2 := by simp
        rw [e]
        exact hsq a a.2)
  rintro _ ⟨f, hf, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h1 hf)

theorem commutator_le_frattiniOf [Finite G] {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) :
    ⁅P, P⁆ ≤ frattiniOf P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : ⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ ∈ frattini ↥P :=
    CFSG.commutator_le_frattini_of_isPGroup (p := 2)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact ⟨_, h1, map_commutatorElement P.subtype ⟨a, ha⟩ ⟨b, hb⟩⟩

theorem mem_frattiniOf_conj {R : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G)) {y : G}
    (hy : y ∈ frattiniOf R) : g * y * g⁻¹ ∈ frattiniOf R := by
  obtain ⟨f, hf, rfl⟩ := hy
  set α := R.normalizerMonoidHom ⟨g, hg⟩ with hα
  have h1 : α f ∈ frattini ↥R := by
    have := CFSG.QuasithinUnique.Setup.Campbell.frattini_map_equiv α
    rw [← this]
    exact ⟨f, hf, rfl⟩
  refine ⟨α f, h1, ?_⟩
  simp [hα]

theorem mem_normalizer_frattiniOf {R : Subgroup G} {t : G} (ht : t ∈ normalizer (R : Set G)) :
    t ∈ normalizer (frattiniOf R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨mem_frattiniOf_conj ht, fun h => ?_⟩
  have := mem_frattiniOf_conj ((normalizer (R : Set G)).inv_mem ht) h
  have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
  rw [e] at this
  exact this

end Generators

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G}

omit [Finite G] in
theorem comm_mem_of_comm {N : Subgroup G} {a b : G} (h : a * b = b * a) : ⁅a, b⁆ ∈ N := by
  rw [commutatorElement_eq_one_iff_mul_comm.mpr h]
  exact N.one_mem

theorem A3A3x.rank1₁ (hD : AppC.C56DoubleA3)
    (hA : A3A3x T M H S L s x z₁ z₂) :
    C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU L : Set G)) (blockU L)
      (zpowers z₁) 2 := by
  obtain ⟨w₁, _, -, -, hw₁C, -, R1, -⟩ := rank1_blocks hD hA.toA3A3
  have h : zpowers z₁ = zpowers w₁ := hA.z₁_gen.trans hw₁C
  rw [h]
  exact R1

theorem A3A3x.x_mem_normalizer_baum (hB : Basic31 T M H S L s)
    (hA : A3A3x T M H S L s x z₁ z₂) : x ∈ normalizer (baum S : Set G) :=
  normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hA.cs.le_T hB.idx_T hA.x_mem)

theorem A3A3x.z₁_mem_commutator (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) : z₁ ∈ ⁅baum S, baum S⁆ := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  have R1 := hA.rank1₁ hD
  have hxN := hA.x_mem_normalizer_baum hB
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hA.a3
  have hx1 : ¬ conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => hA.x_good (h.trans inf_le_right)
  have hx2 : ¬ conjSubgroup (blockU L) x⁻¹ ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => not_conj_inv_le_centralizer hA.x_good (h.trans inf_le_right)
  have hcomm := (R1.commutator_conj hxN hx1 hx2).1
  have hz : z₁ ∈ ⁅blockU L, conjSubgroup (blockU L) x⁆ := by
    rw [hcomm]; exact Subgroup.mem_zpowers z₁
  exact Subgroup.commutator_mono hUB (R1.conj_le_B hxN) hz

theorem A3A3x.cross_comm (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) :
    (∀ a ∈ blockU L, ∀ b ∈ conjR (blockU2 L s) x, a * b = b * a) ∧
    (∀ a ∈ blockU2 L s, ∀ b ∈ conjR (blockU L) x, a * b = b * a) := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  obtain ⟨h0, -⟩ := good_commutation hD hA.toA3A3 hcs.le_T le_rfl hB.idx_T hA.x_mem
    hA.x_not_mem hA.x_good
  have key : ∀ a ∈ blockU L ⊔ conjR (blockU L) x, ∀ b ∈ blockU2 L s ⊔ conjR (blockU2 L s) x,
      a * b = b * a := by
    intro a ha b hb
    have : ⁅a, b⁆ ∈ ⁅blockU L ⊔ conjR (blockU L) x, blockU2 L s ⊔ conjR (blockU2 L s) x⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [h0] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)
  exact ⟨fun a ha b hb => key a (mem_sup_left ha) b (mem_sup_right hb),
    fun a ha b hb => (key b (mem_sup_right hb) a (mem_sup_left ha)).symm⟩

theorem A3A3x.frattini_eq (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) :
    frattiniOf (baum S) = zpowers z₁ ⊔ zpowers z₂ := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  have hxN := hA.x_mem_normalizer_baum hB
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hA.s_mem
  obtain ⟨hU0, hDel, hbD, -, -, -, hx⟩ :=
    hD G T M H S L hcs hA.a3 hA.conjJoin_ne T hcs.le_T le_rfl hB.idx_T
  obtain ⟨-, hRgen, -⟩ := hx x hA.x_mem hA.x_not_mem
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hA.toA3A3.blockU0_eq hU0
  obtain ⟨-, -, -, h4, -⟩ := lemma2_4_30 hD h27_1 G T M H S L s hA.toA3A3
  obtain ⟨-, -, hcommD, -, -⟩ := h4 x hA.x_mem hA.x_not_mem
  have hNc : zpowers z₁ ⊔ zpowers z₂ ≤ centralizer (baum S : Set G) :=
    sup_le (zpowers_le.mpr hA.z₁_mem.2) (zpowers_le.mpr hA.z₂_mem.2)
  have hN : ∀ n ∈ zpowers z₁ ⊔ zpowers z₂, ∀ p ∈ baum S, n * p = p * n := fun n hn p hp =>
    (Subgroup.mem_centralizer_iff.mp (hNc hn) p hp).symm
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hA.a3
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hU₁xB : conjR (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hU₂xB : conjR (blockU2 L s) x ≤ baum S :=
    (C5.conjSubgroup_mono hU₂B x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hU0conj : conjR (blockU0 S L) x = conjR (blockU L) x ⊔ conjR (blockU2 L s) x := by
    rw [hU0eq]; exact C5.conjSubgroup_sup _ _ _
  have hU0L : blockU0 S L ≤ conjJoin S L := by
    rw [hU0eq, hA.join]
    exact sup_le (hA.isA4.le.trans le_sup_left) (hA.isA4s.le.trans le_sup_right)
  have R1 := hA.rank1₁ hD
  have R2 := hA.rank1₂ hD
  have hc1 := (R1.commutator_conj hxN (fun h => hA.x_good (h.trans inf_le_right))
    (fun h => not_conj_inv_le_centralizer hA.x_good (h.trans inf_le_right))).1
  have hc2 := (R2.commutator_conj hxN (fun h => hA.x_good₂ (h.trans inf_le_right))
    (fun h => not_conj_inv_le_centralizer hA.x_good₂ (h.trans inf_le_right))).1
  obtain ⟨hX1, hX2⟩ := hA.cross_comm hD h27_1
  have hBel : IsElemAbelian 2 (blockU0 S L) := by
    rw [hU0eq]
    exact isElemAbelian_sup_of_commute hA.isA4.isElemAbelian_U hA.isA4s.isElemAbelian_U
      (fun a ha b hb => hA.comm_elem a (hA.isA4.le ha) b (hA.isA4s.le hb))
  have hCel : IsElemAbelian 2 (conjR (blockU0 S L) x) := isElemAbelian_conjR hBel x
  have hAB : ∀ a ∈ baumD S L, ∀ b ∈ blockU0 S L, ⁅a, b⁆ ∈ zpowers z₁ ⊔ zpowers z₂ := by
    intro a ha b hb
    exact comm_mem_of_comm (Subgroup.mem_centralizer_iff.mp ha.2 b (hU0L hb)).symm
  have hAC : ∀ a ∈ baumD S L, ∀ c ∈ conjR (blockU0 S L) x, ⁅a, c⁆ ∈ zpowers z₁ ⊔ zpowers z₂ := by
    intro a ha c hc
    have ha' : a ∈ blockD S L := by rw [← hbD]; exact ha
    exact comm_mem_of_comm (hcommD a ha' c (mem_sup_right hc))
  have s1 : ∀ u ∈ blockU L, ∀ c ∈ conjR (blockU0 S L) x, ⁅u, c⁆ ∈ zpowers z₁ ⊔ zpowers z₂ := by
    intro u hu
    have : conjR (blockU0 S L) x ≤ commSub (baum S) (zpowers z₁ ⊔ zpowers z₂) hN u := by
      rw [hU0conj]
      refine sup_le (fun c hc => ⟨hU₁xB hc, ?_⟩) (fun c hc => ⟨hU₂xB hc, ?_⟩)
      · have h' : ⁅u, c⁆ ∈ ⁅blockU L, conjSubgroup (blockU L) x⁆ :=
          Subgroup.commutator_mem_commutator hu hc
        rw [hc1] at h'
        exact mem_sup_left h'
      · exact comm_mem_of_comm (hX1 u hu c hc)
    exact fun c hc => (mem_commSub.mp (this hc)).2
  have s2 : ∀ u ∈ blockU2 L s, ∀ c ∈ conjR (blockU0 S L) x, ⁅u, c⁆ ∈ zpowers z₁ ⊔ zpowers z₂ := by
    intro u hu
    have : conjR (blockU0 S L) x ≤ commSub (baum S) (zpowers z₁ ⊔ zpowers z₂) hN u := by
      rw [hU0conj]
      refine sup_le (fun c hc => ⟨hU₁xB hc, ?_⟩) (fun c hc => ⟨hU₂xB hc, ?_⟩)
      · exact comm_mem_of_comm (hX2 u hu c hc)
      · have h' : ⁅u, c⁆ ∈ ⁅blockU2 L s, conjSubgroup (blockU2 L s) x⁆ :=
          Subgroup.commutator_mem_commutator hu hc
        rw [hc2] at h'
        exact mem_sup_right h'
    exact fun c hc => (mem_commSub.mp (this hc)).2
  have hBC : ∀ b ∈ blockU0 S L, ∀ c ∈ conjR (blockU0 S L) x,
      ⁅b, c⁆ ∈ zpowers z₁ ⊔ zpowers z₂ := by
    intro b hb c hc
    have : blockU0 S L ≤ commSub (baum S) (zpowers z₁ ⊔ zpowers z₂) hN c := by
      rw [hU0eq]
      exact sup_le (fun u hu => ⟨hUB hu, commutatorElement_mem_comm.mp (s1 u hu c hc)⟩)
        (fun u hu => ⟨hU₂B hu, commutatorElement_mem_comm.mp (s2 u hu c hc)⟩)
    exact commutatorElement_mem_comm.mp (mem_commSub.mp (this hb)).2
  have hAcomm : ∀ a ∈ baumD S L, ∀ a' ∈ baumD S L, ⁅a, a'⁆ ∈ zpowers z₁ ⊔ zpowers z₂ :=
    fun a ha a' ha' => comm_mem_of_comm (elemAbelian_comm hDel ha ha')
  have hBcomm : ∀ b ∈ blockU0 S L, ∀ b' ∈ blockU0 S L, ⁅b, b'⁆ ∈ zpowers z₁ ⊔ zpowers z₂ :=
    fun b hb b' hb' => comm_mem_of_comm (elemAbelian_comm hBel hb hb')
  have hCcomm : ∀ c ∈ conjR (blockU0 S L) x, ∀ c' ∈ conjR (blockU0 S L) x,
      ⁅c, c'⁆ ∈ zpowers z₁ ⊔ zpowers z₂ :=
    fun c hc c' hc' => comm_mem_of_comm (elemAbelian_comm hCel hc hc')
  have hcommR := commutators_mem_of_generators hN hRgen hAcomm hBcomm hCcomm hAB hAC hBC
  have hsqR := sq_mem_of_generators hRgen hcommR
    (fun a ha => by rw [hDel.2 a ha]; exact Subgroup.one_mem _)
    (fun b hb => by rw [hBel.2 b hb]; exact Subgroup.one_mem _)
    (fun c hc => by rw [hCel.2 c hc]; exact Subgroup.one_mem _)
  apply le_antisymm
  · exact frattini_le_of_generators hN hcommR hsqR
  · have h2 := commutator_le_frattiniOf (isPGroup_baum hcs)
    exact sup_le (zpowers_le.mpr (h2 (hA.z₁_mem_commutator hD h27_1)))
      (zpowers_le.mpr (h2 (hA.z₂_mem_commutator hD h27_1)))

theorem A3A3x.z₁_ne_z₂ (hA : A3A3x T M H S L s x z₁ z₂) : z₁ ≠ z₂ := by
  intro h
  apply hA.z_ne
  have h1 : z₁ * z₁ = 1 := by simpa [pow_two] using hA.sq₁
  rw [← h]
  exact h1

theorem A3A3x.relIndex_sOne (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) : (sOne S x).relIndex T = 2 := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  have hRS₁ : baum S ≤ sOne S x := le_sup_left
  have h1 : Nat.card (sOne S x) = Nat.card (baum S) * (baum S).relIndex (sOne S x) :=
    C5.card_eq_card_mul_relIndex hRS₁
  have h2 : Nat.card T = Nat.card (sOne S x) * (sOne S x).relIndex T :=
    C5.card_eq_card_mul_relIndex hA.sOne_le_T
  have hk : (baum S).relIndex (sOne S x) ≠ 1 := by
    intro h
    have : sOne S x ≤ baum S := Subgroup.relIndex_eq_one.mp h
    exact hA.x_not_mem ((inf_le_left : baum S ≤ S) (this (mem_sup_right (Subgroup.mem_zpowers x))))
  have hm : (sOne S x).relIndex T ≠ 1 := by
    intro h
    have hT : T ≤ sOne S x := Subgroup.relIndex_eq_one.mp h
    have hsS₁ : s ∈ sOne S x := hT (hcs.le_T hA.s_mem)
    have hsc : s * z₁ = z₁ * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hA.sOne_le_cent₁ hsS₁)
    apply hA.z₁_ne_z₂
    calc z₁ = s⁻¹ * (s * z₁) := by group
      _ = s⁻¹ * (z₁ * s) := by rw [hsc]
      _ = z₂ := by rw [hA.z₂_def]; group
  have hpos : 0 < Nat.card (baum S) := Nat.card_pos
  obtain ⟨k, hkdef⟩ : ∃ k, k = (baum S).relIndex (sOne S x) := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = (sOne S x).relIndex T := ⟨_, rfl⟩
  rw [← hkdef] at h1 hk
  rw [← hmdef] at h2 hm ⊢
  have h3 : Nat.card (baum S) * (k * m) = Nat.card (baum S) * 4 := by
    calc Nat.card (baum S) * (k * m) = Nat.card T := by rw [h2, h1]; ring
      _ = Nat.card (baum S) * 4 := by rw [hB.card_T]; ring
  have h4 : k * m = 4 := Nat.eq_of_mul_eq_mul_left hpos h3
  have hkle : k ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨m, h4.symm⟩
  interval_cases k <;> omega

end Config

end CFSG.QuasithinUnique.DoubleA3

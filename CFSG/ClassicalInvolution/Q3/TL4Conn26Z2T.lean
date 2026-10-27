module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2F
public import CFSG.ClassicalInvolution.Q3.TL4S289ZA
public import CFSG.ClassicalInvolution.Q3.TL4S289Lnk

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Z2T

section Groups

variable {M M' : Type} [Group M] [Group M']

theorem center_eq_bot_of_simple (hs : IsSimpleGroup M) (hna : ∃ a b : M, a * b ≠ b * a) :
    Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem isQuasisimple_of_simple (hs : IsSimpleGroup M) (hna : ∃ a b : M, a * b ≠ b * a) :
    CFSG.IsQuasisimple M := by
  have hZ := center_eq_bot_of_simple hs hna
  have hperf : Group.IsPerfect M := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator M) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  let e : M ≃* M ⧸ Subgroup.center M :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  refine ⟨hperf, e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

theorem innerFour_of_pairs [Finite M] (hZ : Subgroup.center M = ⊥)
    (hconj : ∀ a a' : M, a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → ∃ g : M, g * a * g⁻¹ = a')
    (hα : ∀ (𝒳 : Subgroup (MulAut M)) (hinn : ∀ g : M, MulAut.conj g ∈ 𝒳) (a a' : M),
      a * a = 1 → a ≠ 1 → a' ≠ a → a * a' = a' * a → (∃ g : M, g * a * g⁻¹ = a') →
        alphaOf (Subgroup.closure
          ({⟨MulAut.conj a, hinn a⟩, ⟨MulAut.conj a', hinn a'⟩} : Set ↥𝒳)) = ⊥) :
    ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
      ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
        (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥ := by
  intro 𝒳 hinn A hAin hAsq hA4
  have hinn' : ∀ g : M, MulAut.conj g ∈ 𝒳 := fun g => hinn ⟨g, rfl⟩
  have : Finite (MulAut M) :=
    Finite.of_injective (fun α : MulAut M => (α : M → M)) fun _ _ e => MulEquiv.ext (congrFun e)
  have hconj1 : ∀ a : M, MulAut.conj a = 1 → a = 1 := by
    intro a ha
    have hmem : a ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h : a * g * a⁻¹ = g := by
        have h1 := congrArg (fun φ : MulAut M => φ g) ha
        simpa only [MulAut.conj_apply, MulAut.one_apply] using h1
      calc g * a = a * g * a⁻¹ * a := by rw [h]
        _ = a * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨x, hxA, hx1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    have hb : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr h
    rw [hb, Subgroup.card_bot] at hA4
    omega
  have hx2 : x * x = 1 := hAsq x hxA
  have hzx : Nat.card ↥(Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers x from h)
    omega
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : x ≠ y := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  have hy2 : y * y = 1 := hAsq y hyA
  have hcomm : x * y = y * x := by
    have h := inv_eq_of_mul_eq_one_right (hAsq (x * y) (A.mul_mem hxA hyA))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2] at h
    exact h.symm
  have hAeq : A = Subgroup.closure ({x, y} : Set ↥𝒳) := by
    have hle : Subgroup.closure ({x, y} : Set ↥𝒳) ≤ A := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hxA
      · exact hyA
    have h4 := Bootstrap.card_closure_pair_eq_four hx2 hy2 hx1 hy1 hxy hcomm
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hA4])).symm
  obtain ⟨a, ha⟩ := hAin x hxA
  obtain ⟨b, hb⟩ := hAin y hyA
  have hxa : x = ⟨MulAut.conj a, hinn' a⟩ := Subtype.ext ha.symm
  have hyb : y = ⟨MulAut.conj b, hinn' b⟩ := Subtype.ext hb.symm
  have hval : ∀ z w : ↥𝒳, z = w → (z : MulAut M) = w := fun _ _ h => h ▸ rfl
  have ha1 : a ≠ 1 := fun h => hx1 (by
    rw [hxa]
    apply Subtype.ext
    change MulAut.conj a = 1
    rw [h, map_one])
  have hb1 : b ≠ 1 := fun h => hy1 (by
    rw [hyb]
    apply Subtype.ext
    change MulAut.conj b = 1
    rw [h, map_one])
  have ha2 : a * a = 1 := hconj1 _ (by
    have h := hval _ _ hx2
    rw [hxa] at h
    rw [map_mul]
    exact h)
  have hb2 : b * b = 1 := hconj1 _ (by
    have h := hval _ _ hy2
    rw [hyb] at h
    rw [map_mul]
    exact h)
  have hba : b ≠ a := fun h => hxy (by rw [hxa, hyb, h])
  have hab : a * b = b * a := by
    have h := hval _ _ hcomm
    rw [hxa, hyb] at h
    have h1 : MulAut.conj (a * b * (b * a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul]
      change MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a at h
      rw [h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hconj1 _ h1)
  obtain ⟨g, hg⟩ := hconj a b ha2 ha1 hb2 hb1
  rw [hAeq, hxa, hyb]
  exact hα 𝒳 hinn' a b ha2 ha1 hba hab ⟨g, hg⟩

theorem innerFour_congr (e : M ≃* M')
    (h : ∀ 𝒳 : Subgroup (MulAut M'), Q3NM.innSubgroup M' ≤ 𝒳 →
      ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M') ∈ Q3NM.innSubgroup M') →
        (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥) :
    ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
      ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
        (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥ := by
  intro 𝒳 hinn A hAin hAsq hA4
  have hc : ∀ m : M, MulAut.congr e (MulAut.conj m) = MulAut.conj (e m) := fun m => by
    ext x
    change e (m * e.symm x * m⁻¹) = e m * x * (e m)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  let θ : ↥𝒳 ≃* ↥(𝒳.map (MulAut.congr e).toMonoidHom) :=
    𝒳.equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
  have hinn' : Q3NM.innSubgroup M' ≤ 𝒳.map (MulAut.congr e).toMonoidHom := by
    rintro _ ⟨m', rfl⟩
    refine ⟨MulAut.conj (e.symm m'), hinn ⟨e.symm m', rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm m')) = MulAut.conj m'
    rw [hc, MulEquiv.apply_symm_apply]
  have h1 := h (𝒳.map (MulAut.congr e).toMonoidHom) hinn' (A.map θ.toMonoidHom) ?_ ?_ ?_
  · rw [ExactLayer.alphaOf_map_equiv θ A] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).mp h1
  · rintro _ ⟨a, haA, rfl⟩
    obtain ⟨m, hm⟩ := hAin a haA
    refine ⟨e m, ?_⟩
    change MulAut.conj (e m) = MulAut.congr e (a : MulAut M)
    rw [← hm, hc]
  · rintro _ ⟨a, haA, rfl⟩
    change θ a * θ a = 1
    rw [← map_mul, hAsq a haA, map_one]
  · rw [Subgroup.card_map_of_injective θ.injective, hA4]

end Groups

end Z2T

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J J₂ J₃ : Subgroup Y} {u v : Y}

namespace Z2FrameAt

theorem u_mem_linkLayer (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    u ∈ linkLayer R t :=
  coreAt_le_linkLayerAt hF.memJ (mem_coreAt_of_sq_sq hF.invJ.mem
    (by rw [hF.invJ.sq, one_mul]) (hF.comm_tu hL).symm)

theorem v_mem_linkLayer (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v) :
    v ∈ linkLayer R t :=
  coreAt_le_linkLayerAt hF.memJ₂ (mem_coreAt_of_sq_sq hF.invJ₂.mem
    (by rw [hF.invJ₂.sq, one_mul]) (hF.comm_tv hL).symm)

theorem le_modOdd_of_frame (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v)
    {L : Subgroup (OddQuot t)} (hLc : CFSG.IsComponent L)
    (hm : MovedByAll (Subgroup.closure ({t, u, v} : Set Y)) t L) :
    L ≤ modOdd t (linkLayer R t) := by
  have ht := hL.datum.isUniqueInvolution_core
  have huΛ := hF.u_mem_linkLayer hL
  have hutC := linkLayerAt_le_centralizer huΛ
  have hm3 := mem_closure_three_left t u v
  have huZ := Lemma52Proof.oddQuotMk_not_mem_zpowers (hF.isElemAbelian hL) hm3.1 ht.ne_one
    hm3.2.1 hF.invJ.ne_one (hF.ne_tu hL).symm hutC
  exact S289.le_of_moved (S289.modOdd_normal fun _ hc _ hy => conj_mem_linkLayer hL hc hy) hLc
    (oddQuotMk_mem_modOdd huΛ hutC) (hm _ (oddQuotMk_mem_modOdd hm3.2.1 hutC) huZ)

end Z2FrameAt

end Cit3

section Cit3b


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J J₂ J₃ : Subgroup Y} {u v : Y}

namespace Z2FrameAt

theorem hyp51At_t (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v)
    (hsimp : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)))
    (hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a)
    (hinv : ∀ a : ↥(linkGrp R t), a * a = 1 → a ∈ genFittingFStar ↥(linkGrp R t))
    (hconj : ∀ a a' : ↥(genFittingFStar ↥(linkGrp R t)), a * a = 1 → a ≠ 1 → a' * a' = 1 →
      a' ≠ 1 → ∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a')
    (hα : ∀ (𝒳 : Subgroup (MulAut ↥(genFittingFStar ↥(linkGrp R t))))
      (hinn : ∀ g : ↥(genFittingFStar ↥(linkGrp R t)), MulAut.conj g ∈ 𝒳)
      (a a' : ↥(genFittingFStar ↥(linkGrp R t))),
      a * a = 1 → a ≠ 1 → a' ≠ a → a * a' = a' * a →
        (∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a') →
        alphaOf (Subgroup.closure
          ({⟨MulAut.conj a, hinn a⟩, ⟨MulAut.conj a', hinn a'⟩} : Set ↥𝒳)) = ⊥) :
    Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) t := by
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u v
  have huΛ := hF.u_mem_linkLayer hL
  have hvΛ := hF.v_mem_linkLayer hL
  have hutC : u ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer huΛ
  have hvtC : v ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer hvΛ
  have hFn : (genFittingFStar ↥(linkGrp R t)).Normal := genFittingFStar_normal _
  have hQF := Z2T.isQuasisimple_of_simple hsimp hnab
  have hZF := Z2T.center_eq_bot_of_simple hsimp hnab
  have huN' : oddQuotMk t ⟨u, hutC⟩ ∈ modOdd t (linkLayer R t) := oddQuotMk_mem_modOdd huΛ hutC
  have hvN' : oddQuotMk t ⟨v, hvtC⟩ ∈ modOdd t (linkLayer R t) := oddQuotMk_mem_modOdd hvΛ hvtC
  have hsqF : ∀ (c : Y) (hc : c ∈ Subgroup.centralizer ({t} : Set Y))
      (hcN : oddQuotMk t ⟨c, hc⟩ ∈ modOdd t (linkLayer R t)), c * c = 1 →
      (S289.linkVtxEquiv hL ⟨_, hcN⟩ : ↥(linkGrp R t)) ∈ genFittingFStar ↥(linkGrp R t) := by
    intro c hc hcN hcc
    refine hinv _ ?_
    rw [← map_mul]
    have h1 : (⟨oddQuotMk t ⟨c, hc⟩, hcN⟩ : ↥(modOdd t (linkLayer R t))) *
        ⟨oddQuotMk t ⟨c, hc⟩, hcN⟩ = 1 := by
      apply Subtype.ext
      change oddQuotMk t ⟨c, hc⟩ * oddQuotMk t ⟨c, hc⟩ = 1
      rw [← map_mul]
      have h2 : (⟨c, hc⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) * ⟨c, hc⟩ = 1 :=
        Subtype.ext hcc
      rw [h2, map_one]
    rw [h1, map_one]
  have heuF := hsqF u hutC huN' hF.invJ.sq
  have hevF := hsqF v hvtC hvN' hF.invJ₂.sq
  have huZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one hm3.2.1 hF.invJ.ne_one
    (hF.ne_tu hL).symm hutC
  have hCeq : ∀ L : Subgroup (OddQuot t), CFSG.IsComponent L →
      (hLN : L ≤ modOdd t (linkLayer R t)) →
      (∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩) →
      (L.subgroupOf (modOdd t (linkLayer R t))).map (S289.linkVtxEquiv hL).toMonoidHom =
        genFittingFStar ↥(linkGrp R t) := by
    intro L hLc hLN hmu
    have hC : CFSG.IsComponent ((L.subgroupOf (modOdd t (linkLayer R t))).map
        (S289.linkVtxEquiv hL).toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv _ (LocalCores.component_overgroup hLc hLN)
    have hmuC : ∃ c ∈ (L.subgroupOf (modOdd t (linkLayer R t))).map
        (S289.linkVtxEquiv hL).toMonoidHom, S289.linkVtxEquiv hL ⟨_, huN'⟩ * c ≠
          c * S289.linkVtxEquiv hL ⟨_, huN'⟩ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, hne⟩ := hmu
      exact hne (S289.commute_of_map (S289.linkVtxEquiv hL) hLN huN' hcon y hy)
    have hle := S289.le_of_moved hFn hC heuF hmuC
    have htop := S289.eq_top_of_isComponent hQF (LocalCores.component_overgroup hC hle)
    exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
  have hmuOf : ∀ L : Subgroup (OddQuot t),
      MovedByAll (Subgroup.closure ({t, u, v} : Set Y)) t L →
      ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩ :=
    fun L hm => hm _ (oddQuotMk_mem_modOdd hm3.2.1 hutC) huZ
  refine ⟨fun L₁ L₂ h1 h2 hm1 hm2 => ?_, fun L hLc hm => ?_⟩
  · have hN1 := hF.le_modOdd_of_frame hL h1 hm1
    have hN2 := hF.le_modOdd_of_frame hL h2 hm2
    have e1 := hCeq L₁ h1 hN1 (hmuOf L₁ hm1)
    have e2 := hCeq L₂ h2 hN2 (hmuOf L₂ hm2)
    have h3 := Subgroup.map_injective (S289.linkVtxEquiv hL).injective (e1.trans e2.symm)
    have h4 := Subgroup.subgroupOf_inj.mp h3
    rwa [inf_of_le_left hN1, inf_of_le_left hN2] at h4
  have hLN := hF.le_modOdd_of_frame hL hLc hm
  have hCF := hCeq L hLc hLN (hmuOf L hm)
  have huL : oddQuotMk t ⟨u, hutC⟩ ∈ L :=
    S289.mem_of_map_mem (S289.linkVtxEquiv hL) huN' (by rw [hCF]; exact heuF)
  have hvL : oddQuotMk t ⟨v, hvtC⟩ ∈ L :=
    S289.mem_of_map_mem (S289.linkVtxEquiv hL) hvN' (by rw [hCF]; exact hevF)
  have hncl := hF.not_mem_closure hL
  have hct : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hcu : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huv1 : u * v ≠ 1 := fun e =>
    hncl ((eq_inv_of_mul_eq_one_right e) ▸ Subgroup.inv_mem _ hcu)
  have huvt : u * v ≠ t := fun e => hncl (by
    rw [show v = u⁻¹ * t by rw [← e]; group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcu) hct)
  have huvB := Subgroup.mul_mem _ hm3.2.1 hm3.2.2
  have huvC : u * v ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mul_mem _ hutC hvtC
  have hmu := hmuOf L hm
  have hmv := hm _ (oddQuotMk_mem_modOdd hm3.2.2 hvtC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one hm3.2.2 hF.invJ₂.ne_one
      (hF.ne_tv hL).symm hvtC)
  have hmuv : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨v, hvtC⟩ * y ≠
      y * (oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨v, hvtC⟩) := by
    rw [← map_mul]
    exact hm _ (oddQuotMk_mem_modOdd huvB huvC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one huvB huv1 huvt huvC)
  let eL : ↥L ≃* ↥(genFittingFStar ↥(linkGrp R t)) :=
    ((Subgroup.subgroupOfEquivOfLe hLN).symm.trans
      ((L.subgroupOf (modOdd t (linkLayer R t))).equivMapOfInjective
        (S289.linkVtxEquiv hL).toMonoidHom (S289.linkVtxEquiv hL).injective)).trans
      (MulEquiv.subgroupCongr hCF)
  have hαL := Z2T.innerFour_congr eL (Z2T.innerFour_of_pairs hZF hconj hα)
  exact S289.alphaOf_eq_bot_of_innerFour hB hutC hvtC hαL huL hvL hmu hmv hmuv

end Z2FrameAt

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrFrames
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrHyp51
public import CFSG.ClassicalInvolution.Q3.TL4S289U3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Blueprint
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K'' : Subgroup Y} {u w : Y}


structure LinkExitData (R : Subgroup Y) (t : Y) (L₀ : Subgroup ↥(linkGrp R t)) : Prop where
  normal : L₀.Normal
  simple : IsSimpleGroup ↥L₀
  model : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
    (LieModel ↥L₀ .PSL 3 p f ∨ LieModel ↥L₀ .PSU 3 p f)
  inv : ∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a → a ∈ L₀
  dich : ∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
    ∀ P : Subgroup ↥(linkGrp R t), IsSylow2In P M → ∀ β : MulAut ↥(linkGrp R t), β * β = 1 →
      (∀ x ∈ P, β x = x) → (∀ y ∈ L₀, β y = y) ∨ (∀ y ∈ L₀, β y = a * y * a⁻¹)

theorem member_inv_mem_of_normal' {X : Type} [Group X] {R' : Subgroup X} {Φ : Set (Subgroup X)}
    (hfam : CoreAssembly.conjClass (tightCore R') = Φ) {z : X}
    (hz : IsUniqueInvolution (tightCore R') z) {L₀ : Subgroup X} [L₀.Normal] (hzL : z ∈ L₀) :
    ∀ M ∈ Φ, ∀ m : X, IsUniqueInvolution M m → m ∈ L₀ := by
  intro M hM m hm
  have hM' : M ∈ CoreAssembly.conjClass (tightCore R') := hfam ▸ hM
  obtain ⟨g, hg⟩ := hM'
  have h1 := hz.conj g
  rw [show conjSub g (tightCore R') = M from hg] at h1
  rw [hm.eq h1]
  exact Subgroup.Normal.conj_mem ‹L₀.Normal› z hzL g

theorem exitLU_dich_all {X : Type} [Group X] [Finite X] {R' : Subgroup X} {S' : Sylow 2 ↥R'} {z : X}
    (hd : TightDatum R' S' z) (hcore : tightCore R' = R') {L₀ : Subgroup X} [L₀.Normal]
    (hdich : ∀ β : MulAut X, β * β = 1 → (∀ s ∈ sylowSet S', β s = s) →
      (∀ y ∈ L₀, β y = y) ∨ (∀ y ∈ L₀, β y = z * y * z⁻¹)) {Φ : Set (Subgroup X)}
    (hfam : CoreAssembly.conjClass (tightCore R') = Φ) :
    ∀ M ∈ Φ, ∀ a : X, IsUniqueInvolution M a → ∀ P : Subgroup X, IsSylow2In P M →
      ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) →
        (∀ y ∈ L₀, β y = y) ∨ (∀ y ∈ L₀, β y = a * y * a⁻¹) := by
  intro M hM a ha P hP β hβ2 hβP
  have hM' : M ∈ CoreAssembly.conjClass (tightCore R') := hfam ▸ hM
  obtain ⟨g, hg⟩ := hM'
  have hgM : conjSub g R' = M := by rw [← hcore]; exact hg
  have hz := hd.isUniqueInvolution_core
  rw [hcore] at hz
  have hag : a = g * z * g⁻¹ := by
    have h1 := hz.conj g
    rw [hgM] at h1
    exact ha.eq h1
  have hP' : IsSylow2In (conjSub g⁻¹ P) R' := by
    have h1 := S1916.IsSylow2In.conj hP g⁻¹
    rwa [← hgM, conjSub_inv_conjSub] at h1
  obtain ⟨c, hcR, hcP⟩ := S1916.IsSylow2In.exists_conj hP' (isSylow2In_map_subtype R' S')
  set k : X := c * g⁻¹ with hk
  have hkP : conjSub k P = sylowSet S' := by
    rw [hk, conjSub_mul]
    exact hcP
  set β' : MulAut X := MulAut.conj k * β * (MulAut.conj k)⁻¹ with hβ'
  have hβ'2 : β' * β' = 1 := by
    have : β' * β' = MulAut.conj k * (β * β) * (MulAut.conj k)⁻¹ := by rw [hβ']; group
    rw [this, hβ2]
    group
  have hβ'app : ∀ y : X, β' y = k * β (k⁻¹ * y * k) * k⁻¹ := fun y => by
    rw [hβ', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
  have hβ'S : ∀ s ∈ sylowSet S', β' s = s := by
    intro s hs
    rw [← hkP] at hs
    rw [mem_conjSub_iff] at hs
    rw [hβ'app, hβP _ hs]
    group
  have hzc : c⁻¹ * z * c = z := by
    have hzc' : z * c = c * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (S289G.le_centralizer_of_isUniqueInvolution hz hcR)).symm
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = z := by rw [hzc']; group
  have hkz : k⁻¹ * z * k = a := by
    rw [hag, hk]
    calc (c * g⁻¹)⁻¹ * z * (c * g⁻¹) = g * (c⁻¹ * z * c) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hzc]
  have hLk : ∀ y ∈ L₀, k * y * k⁻¹ ∈ L₀ := fun y hy => Subgroup.Normal.conj_mem ‹L₀.Normal› y hy k
  have hβ'k : ∀ y₀ : X, β y₀ = k⁻¹ * β' (k * y₀ * k⁻¹) * k := by
    intro y₀
    rw [hβ'app, show k⁻¹ * (k * y₀ * k⁻¹) * k = y₀ by group]
    group
  rcases hdich β' hβ'2 hβ'S with h1 | h2
  · left
    intro y₀ hy₀
    rw [hβ'k, h1 _ (hLk y₀ hy₀)]
    group
  · right
    intro y₀ hy₀
    rw [hβ'k, h2 _ (hLk y₀ hy₀), ← hkz]
    group

theorem linkExitData_of_linkS (hL : TightLargeHypR r n Y R S t) (hS : LinkSR R t) :
    ∃ L₀ : Subgroup ↥(linkGrp R t), LinkExitData R t L₀ := by
  classical
  obtain ⟨-, -, R', S', z', hR', hd, hE, hfam⟩ := hS
  obtain ⟨L₀, hL₀n, hL₀s, hL₀m, hzL, hdich, -⟩ := hE
  have hΦ : TypeRFam r (linkFam R t) := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hcore : tightCore R' = R' := hΦ.closure_twoElts hR'
  haveI := hL₀n
  refine ⟨L₀, ⟨hL₀n, hL₀s, hL₀m, ?_, ?_⟩⟩
  · exact member_inv_mem_of_normal' hfam hd.isUniqueInvolution_core hzL
  · exact exitLU_dich_all hd hcore (fun β hβ2 hβS => hdich β hβ2 hβS) hfam

theorem commute_of_conjAut_restrict {Q Z : Type} [Group Q] [Group Z] {N : Subgroup Q} [N.Normal]
    (e : ↥N ≃* Z) {L : Subgroup Q} (hLN : L ≤ N) {w : Q} {L₀ : Subgroup Z}
    (hL₀ : (L.subgroupOf N).map e.toMonoidHom = L₀) (h : ∀ y ∈ L₀, S289.conjAut e w y = y) :
    ∀ y ∈ L, w * y = y * w := by
  intro y hy
  have hmem : e ⟨y, hLN hy⟩ ∈ L₀ := by
    rw [← hL₀]
    exact ⟨⟨y, hLN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have h1 := h _ hmem
  rw [S289.conjAut_apply] at h1
  have h2 : w * y * w⁻¹ = y := congrArg Subtype.val (e.injective h1)
  calc w * y = w * y * w⁻¹ * w := by group
    _ = y * w := by rw [h2]

theorem commute_of_conjAut_conj_restrict {Q Z : Type} [Group Q] [Group Z] {N : Subgroup Q}
    [N.Normal] (e : ↥N ≃* Z) {L : Subgroup Q} (hLN : L ≤ N) {w a : Q} (ha : a ∈ N)
    (ha2 : a * a = 1) {L₀ : Subgroup Z} (hL₀ : (L.subgroupOf N).map e.toMonoidHom = L₀)
    (h : ∀ y ∈ L₀, S289.conjAut e w y = e ⟨a, ha⟩ * y * (e ⟨a, ha⟩)⁻¹) :
    ∀ y ∈ L, a * w * y = y * (a * w) := by
  intro y hy
  have hmem : e ⟨y, hLN hy⟩ ∈ L₀ := by
    rw [← hL₀]
    exact ⟨⟨y, hLN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have h1 := h _ hmem
  rw [S289.conjAut_apply] at h1
  have h1' : e ⟨w * y * w⁻¹, Subgroup.Normal.conj_mem inferInstance y (hLN hy) w⟩ =
      e (⟨a, ha⟩ * ⟨y, hLN hy⟩ * ⟨a, ha⟩⁻¹) := by
    rw [h1, map_mul, map_mul, map_inv]
  have h2 : w * y * w⁻¹ = a * y * a⁻¹ := congrArg Subtype.val (e.injective h1')
  calc a * w * y = a * (w * y * w⁻¹) * w := by group
    _ = a * (a * y * a⁻¹) * w := by rw [h2]
    _ = (a * a) * y * a⁻¹ * w := by group
    _ = y * (a * w) := by
      rw [ha2, one_mul, inv_eq_of_mul_eq_one_right ha2, mul_assoc]

theorem commute_of_linkW (hL : TightLargeHypR r n Y R S t) (hW : LinkWR R t) {J' : Subgroup Y}
    {t' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t') (ht'Λ : t' ∈ linkLayer R t) {L : Subgroup (OddQuot t)}
    (hLc : IsComponent L) (hLN : L ≤ modOdd t (linkLayer R t)) :
    ∀ y ∈ L, oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩ * y =
      y * oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩ := by
  set e := S289.linkVtxEquiv hL with he
  have ht'N' := oddQuotMk_mem_modOdd ht'Λ (linkLayerAt_le_centralizer ht'Λ)
  have hC : IsComponent ((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv e (LocalCores.component_overgroup hLc hLN)
  have hau := S289.isUniqueInvolution_link_of hL hJ' ht' ht'Λ
  obtain ⟨P, hPn, hP2, haP⟩ := hW.1 _ (subgroupOf_mem_linkRestrict (t := t) hJ') _ hau
  have hcomm := commute_of_mem_normal_isPGroup hC hPn hP2 haP
  exact S289.commute_of_map e hLN ht'N' (fun c hc => hcomm c hc)

theorem component_eq_of_linkExit (hL : TightLargeHypR r n Y R S t) {L₀ : Subgroup ↥(linkGrp R t)}
    (hE : LinkExitData R t L₀) {J' : Subgroup Y} {t' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t') (ht'Λ : t' ∈ linkLayer R t) {L : Subgroup (OddQuot t)}
    (hLc : IsComponent L) (hLN : L ≤ modOdd t (linkLayer R t))
    (hmt : ∃ y ∈ L, oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩ * y ≠
      y * oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩) :
    (L.subgroupOf (modOdd t (linkLayer R t))).map (S289.linkVtxEquiv hL).toMonoidHom = L₀ := by
  set e := S289.linkVtxEquiv hL with he
  have ht'N' := oddQuotMk_mem_modOdd ht'Λ (linkLayerAt_le_centralizer ht'Λ)
  have hC : IsComponent ((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv e (LocalCores.component_overgroup hLc hLN)
  have hau := S289.isUniqueInvolution_link_of hL hJ' ht' ht'Λ
  have hau' := hE.inv _ (subgroupOf_mem_linkRestrict (t := t) hJ') _ hau
  have hmuC : ∃ c ∈ (L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom,
      e ⟨oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩, ht'N'⟩ * c ≠
        c * e ⟨oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩, ht'N'⟩ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hne⟩ := hmt
    exact hne (S289.commute_of_map e hLN ht'N' hcon y hy)
  have hCle := S289.le_of_moved hE.normal hC hau' hmuC
  exact S289.eq_of_le_of_exitType hC (Or.inl ⟨hE.simple, hE.model⟩) hCle

theorem not_movedByAll_t_of_linkW (hL : TightLargeHypR r n Y R S t)
    (hF : StarFrameAt R t J K'' u w) (hW : LinkWR R t) {L : Subgroup (OddQuot t)}
    (hLc : IsComponent L) : ¬ MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) t L := by
  intro hm
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u w
  have huΛ := S289.u_mem_linkLayer hL hF
  have hutC : u ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer huΛ
  have htu : u ≠ t := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  have hLN := S289.le_modOdd_of_frame hL hF hLc hm
  obtain ⟨y, hy, hne⟩ := hm _ (oddQuotMk_mem_modOdd hm3.2.1 hutC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one hm3.2.1 hF.invJ.ne_one htu hutC)
  exact hne (commute_of_linkW hL hW hF.memJ hF.invJ huΛ hLc hLN y hy)

theorem hyp51At_t_of_linkW (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w)
    (hW : LinkWR R t) : Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) t :=
  ⟨fun _ _ h₁ _ m₁ _ => (not_movedByAll_t_of_linkW hL hF hW h₁ m₁).elim,
    fun _ hLc m => (not_movedByAll_t_of_linkW hL hF hW hLc m).elim⟩

theorem hyp51At_t_of_linkS
    (hα : ∀ (M : Type) [Group M] [Finite M], IsSimpleGroup M →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel M .PSL 3 p f ∨ LieModel M .PSU 3 p f)) →
      ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
        ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
          (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥)
    (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w)
    {L₀ : Subgroup ↥(linkGrp R t)} (hE : LinkExitData R t L₀) :
    Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) t := by
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u w
  have huΛ := S289.u_mem_linkLayer hL hF
  have hwΛ := S289.w_mem_linkLayer hL hF
  have hutC : u ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer huΛ
  have hwtC : w ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer hwΛ
  have huN' := oddQuotMk_mem_modOdd huΛ hutC
  have hwN' := oddQuotMk_mem_modOdd hwΛ hwtC
  have hncl := hF.not_mem_closure hL
  have hct : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hcu : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htu : u ≠ t := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  have htw : w ≠ t := fun e => hncl (e ▸ hct)
  have huw1 : u * w ≠ 1 := fun e => hncl ((eq_inv_of_mul_eq_one_right e) ▸ Subgroup.inv_mem _ hcu)
  have huwt : u * w ≠ t := fun e => hncl (by
    rw [show w = u⁻¹ * t by rw [← e]; group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcu) hct)
  have huwB := Subgroup.mul_mem _ hm3.2.1 hm3.2.2
  have huwC : u * w ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mul_mem _ hutC hwtC
  set e := S289.linkVtxEquiv hL with he
  have hJm := subgroupOf_mem_linkRestrict (t := t) hF.memJ
  have hmov : ∀ L : Subgroup (OddQuot t),
      MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) t L →
      (∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩) ∧
      (∃ y ∈ L, oddQuotMk t ⟨w, hwtC⟩ * y ≠ y * oddQuotMk t ⟨w, hwtC⟩) ∧
      (∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩ * y ≠
        y * (oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩)) := by
    intro L hm
    refine ⟨hm _ (oddQuotMk_mem_modOdd hm3.2.1 hutC) (Lemma52Proof.oddQuotMk_not_mem_zpowers hB
      hm3.1 ht.ne_one hm3.2.1 hF.invJ.ne_one htu hutC), hm _ (oddQuotMk_mem_modOdd hm3.2.2 hwtC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one hm3.2.2 hF.invK.ne_one htw hwtC),
      ?_⟩
    rw [← map_mul]
    exact hm _ (oddQuotMk_mem_modOdd huwB huwC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one huwB huw1 huwt huwC)
  have hcoreC : ∀ L : Subgroup (OddQuot t), IsComponent L →
      MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) t L →
      L ≤ modOdd t (linkLayer R t) ∧
        (L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom = L₀ := by
    intro L hLc hm
    have hLN := S289.le_modOdd_of_frame hL hF hLc hm
    exact ⟨hLN, component_eq_of_linkExit hL hE hF.memJ hF.invJ huΛ hLc hLN (hmov L hm).1⟩
  refine ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ => ?_, fun L hLc hm => ?_⟩
  · obtain ⟨hN₁, e₁⟩ := hcoreC L₁ h₁ m₁
    obtain ⟨hN₂, e₂⟩ := hcoreC L₂ h₂ m₂
    have h3 := Subgroup.map_injective e.injective (e₁.trans e₂.symm)
    have h4 := Subgroup.subgroupOf_inj.mp h3
    rwa [inf_of_le_left hN₁, inf_of_le_left hN₂] at h4
  · obtain ⟨hLN, hCeq⟩ := hcoreC L hLc hm
    obtain ⟨hmu, hmw, hmuw⟩ := hmov L hm
    have hau' := hE.inv _ hJm _ (S289.isUniqueInvolution_link_u hL hF)
    have huL : oddQuotMk t ⟨u, hutC⟩ ∈ L :=
      S289.mem_of_map_mem e huN' (by rw [hCeq]; exact hau')
    have hwL : oddQuotMk t ⟨w, hwtC⟩ ∈ L := S289.mem_of_map_mem e hwN' (by
      rw [hCeq]
      exact hE.inv _ (subgroupOf_mem_linkRestrict (t := t) hF.memK) _
        (S289.isUniqueInvolution_link_w hL hF))
    set eL : ↥L ≃* ↥((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hLN).symm.trans
        ((L.subgroupOf (modOdd t (linkLayer R t))).equivMapOfInjective e.toMonoidHom e.injective)
      with heL
    let eF : ↥L ≃* ↥L₀ := eL.trans (MulEquiv.subgroupCongr hCeq)
    obtain ⟨p, f, hp, hp2, hk'⟩ := hE.model
    haveI := hE.simple
    have hLs : IsSimpleGroup ↥L := eF.isSimpleGroup
    have hLm : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (LieModel ↥L .PSL 3 p f ∨ LieModel ↥L .PSU 3 p f) :=
      ⟨p, f, hp, hp2, hk'.imp (LieType.CurtisTits.lieModel_of_mulEquiv eF.symm)
        (LieType.CurtisTits.lieModel_of_mulEquiv eF.symm)⟩
    exact S289.alphaOf_eq_bot_of_innerFour hB hutC hwtC (hα ↥L hLs hLm) huL hwL hmu hmw hmuw

theorem false_at_t_of_linkS (hL : TightLargeHypR r n Y R S t) {L₀ : Subgroup ↥(linkGrp R t)}
    (hE : LinkExitData R t L₀) {J' K''' : Subgroup Y} {t' w' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t')
    (hK : K''' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J')
    (hw : IsUniqueInvolution K''' w') (ht'C : t' ∈ Subgroup.centralizer ({t} : Set Y))
    (hwt : w' ∈ Subgroup.centralizer ({t} : Set Y)) {L : Subgroup (OddQuot t)}
    (hLc : IsComponent L)
    (hmt : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * y ≠ y * oddQuotMk t ⟨t', ht'C⟩)
    (hmw : ∃ y ∈ L, oddQuotMk t ⟨w', hwt⟩ * y ≠ y * oddQuotMk t ⟨w', hwt⟩)
    (hmtw : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩ * y ≠
      y * (oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩)) : False := by
  have ht := hL.datum.isUniqueInvolution_core
  have htt' : t * t' = t' * t :=
    Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen ht hJ' ht'
  have ht'Λ : t' ∈ linkLayer R t := coreAt_le_linkLayerAt hJ' (mem_coreAt_of_sq_sq ht'.mem
    (by rw [ht'.sq, one_mul]) htt'.symm)
  have hNor : (modOdd t (linkLayer R t)).Normal :=
    S289.modOdd_normal fun _ hc _ hy => conj_mem_linkLayer hL hc hy
  have hLN : L ≤ modOdd t (linkLayer R t) :=
    S289.le_of_moved hNor hLc (oddQuotMk_mem_modOdd ht'Λ ht'C) hmt
  obtain ⟨P, hP, hPc, hPw⟩ := S289.exists_sylow_coreAt hL hJ' ht' hK hw hwt
  have hwb2 : oddQuotMk t ⟨w', hwt⟩ * oddQuotMk t ⟨w', hwt⟩ = 1 := by
    rw [← map_mul, show (⟨w', hwt⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) * ⟨w', hwt⟩ = 1
      from Subtype.ext hw.sq, map_one]
  have ht'b2 : oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨t', ht'C⟩ = 1 := by
    rw [← map_mul, show (⟨t', ht'C⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) * ⟨t', ht'C⟩ = 1
      from Subtype.ext ht'.sq, map_one]
  have hβP : ∀ x ∈ (P.subgroupOf (linkLayer R t)).map (linkLayerHom' hL),
      S289.conjAut (S289.linkVtxEquiv hL) (oddQuotMk t ⟨w', hwt⟩) x = x := by
    rintro _ ⟨⟨p, hpΛ⟩, hp, rfl⟩
    rw [← S289.linkVtxEquiv_eq hL hpΛ]
    refine S289.conjAut_apply_of_commute _ _ ?_
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hPw (Subgroup.mem_subgroupOf.mp hp))).symm)
  have hCeq := component_eq_of_linkExit hL hE hJ' ht' ht'Λ hLc hLN hmt
  rcases hE.dich _ (subgroupOf_mem_linkRestrict (t := t) hJ') _
    (S289.isUniqueInvolution_link_of hL hJ' ht' ht'Λ) _
    (S289.isSylow2In_map_member hL hJ' hP hPc) _ (S289.conjAut_mul_self _ hwb2) hβP with h1 | h1
  · obtain ⟨y, hy, hne⟩ := hmw
    exact hne (commute_of_conjAut_restrict _ hLN hCeq h1 y hy)
  · obtain ⟨y, hy, hne⟩ := hmtw
    exact hne (commute_of_conjAut_conj_restrict _ hLN (oddQuotMk_mem_modOdd ht'Λ ht'C) ht'b2
      hCeq h1 y hy)

theorem false_at_t_of_linkW (hL : TightLargeHypR r n Y R S t) (hW : LinkWR R t)
    {J' : Subgroup Y} {t' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t') (ht'C : t' ∈ Subgroup.centralizer ({t} : Set Y))
    {L : Subgroup (OddQuot t)} (hLc : IsComponent L)
    (hmt : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * y ≠ y * oddQuotMk t ⟨t', ht'C⟩) : False := by
  have ht := hL.datum.isUniqueInvolution_core
  have htt' : t * t' = t' * t :=
    Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen ht hJ' ht'
  have ht'Λ : t' ∈ linkLayer R t := coreAt_le_linkLayerAt hJ' (mem_coreAt_of_sq_sq ht'.mem
    (by rw [ht'.sq, one_mul]) htt'.symm)
  have hNor : (modOdd t (linkLayer R t)).Normal :=
    S289.modOdd_normal fun _ hc _ hy => conj_mem_linkLayer hL hc hy
  have hLN : L ≤ modOdd t (linkLayer R t) :=
    S289.le_of_moved hNor hLc (oddQuotMk_mem_modOdd ht'Λ ht'C) hmt
  obtain ⟨y, hy, hne⟩ := hmt
  exact hne (commute_of_linkW hL hW hJ' ht' ht'Λ hLc hLN y hy)

theorem hyp51At_u_of_vertexT (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w)
    (hT : ∀ (J' K''' : Subgroup Y) (t' w' : Y),
      J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      IsUniqueInvolution J' t' →
      K''' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J' → IsUniqueInvolution K''' w' →
      ∀ (ht'C : t' ∈ Subgroup.centralizer ({t} : Set Y))
        (hwt : w' ∈ Subgroup.centralizer ({t} : Set Y)) (L' : Subgroup (OddQuot t)),
        IsComponent L' → (∃ y ∈ L', oddQuotMk t ⟨t', ht'C⟩ * y ≠ y * oddQuotMk t ⟨t', ht'C⟩) →
        (∃ y ∈ L', oddQuotMk t ⟨w', hwt⟩ * y ≠ y * oddQuotMk t ⟨w', hwt⟩) →
        (∃ y ∈ L', oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩ * y ≠
          y * (oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩)) → False) :
    Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) u := by
  have hnone : ∀ L : Subgroup (OddQuot u), IsComponent L →
      ¬ MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) u L := by
    intro L hLc hm
    have ht := hL.datum.isUniqueInvolution_core
    have hB := hF.isElemAbelian hL
    have hm3 := mem_closure_three_left t u w
    have hncl := hF.not_mem_closure hL
    have htu : t ∈ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL)
    have hwu : w ∈ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_uw hL).symm
    have hct : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
    have hcu : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
    have htu' : t ≠ u := fun e =>
      hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
    have hwu' : w ≠ u := fun e => hncl (e ▸ hcu)
    have htw1 : t * w ≠ 1 := fun e =>
      hncl ((eq_inv_of_mul_eq_one_right e) ▸ Subgroup.inv_mem _ hct)
    have htwu : t * w ≠ u := fun e => hncl (by
      rw [show w = t⁻¹ * u by rw [← e]; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hct) hcu)
    have htwB := Subgroup.mul_mem _ hm3.1 hm3.2.2
    have htwC : t * w ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mul_mem _ htu hwu
    have hmt := hm _ (oddQuotMk_mem_modOdd hm3.1 htu)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one hm3.1 ht.ne_one htu' htu)
    have hmw := hm _ (oddQuotMk_mem_modOdd hm3.2.2 hwu)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one hm3.2.2 hF.invK.ne_one
        hwu' hwu)
    have hmtw : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩ * y ≠
        y * (oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩) := by
      rw [← map_mul]
      exact hm _ (oddQuotMk_mem_modOdd htwB htwC)
        (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one htwB htw1 htwu htwC)
    exact S289.vertexU_cps hL hF.memJ hF.invJ hF.memK hF.invK htu hwu hLc hmt hmw hmtw
      (C := False) fun _ _ _ _ hJ' ht' hK' hw' ht'C hwt _ hL'c hmt' hmw' hmtw' _ _ =>
        hT _ _ _ _ hJ' ht' hK' hw' ht'C hwt _ hL'c hmt' hmw' hmtw'
  exact ⟨fun _ _ h₁ _ m₁ _ => (hnone _ h₁ m₁).elim, fun _ hLc m => (hnone _ hLc m).elim⟩

theorem hyp51_starFrame_of_shape (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hα : ∀ (M : Type) [Group M] [Finite M], IsSimpleGroup M →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel M .PSL 3 p f ∨ LieModel M .PSU 3 p f)) →
      ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
        ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
          (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥)
    (hL : TightLargeHypR r n Y R S t) (hcase : LinkWR R t ∨ LinkSR R t)
    (hF : StarFrameAt R t J K'' u w) : Hyp51 (Subgroup.closure ({t, u, w} : Set Y)) := by
  obtain ⟨g, hg, hgt, hgu, hgw⟩ := starFrame_orbit_r hL hF
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u w
  have hvtu := hyp51At_mul_of_edge_four_le hr hNo h4 hL hF.memJ hF.invJ hB hm3.1 hm3.2.1
  have hvt : Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) t ∧
      Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) u := by
    rcases hcase with hW | hS
    · exact ⟨hyp51At_t_of_linkW hL hF hW, hyp51At_u_of_vertexT hL hF
        fun _ _ _ _ hJ' ht' _ _ ht'C _ _ hL'c hmt' _ _ =>
          false_at_t_of_linkW hL hW hJ' ht' ht'C hL'c hmt'⟩
    · obtain ⟨L₀, hE⟩ := linkExitData_of_linkS hL hS
      exact ⟨hyp51At_t_of_linkS hα hL hF hE, hyp51At_u_of_vertexT hL hF
        fun _ _ _ _ hJ' ht' hK hw ht'C hwt _ hL'c hmt hmw hmtw =>
          false_at_t_of_linkS hL hE hJ' ht' hK hw ht'C hwt hL'c hmt hmw hmtw⟩
  exact hyp51_of_three_vertices hL.datum.isUniqueInvolution_core.sq hF.invJ.sq (hF.comm_tu hL)
    (hF.comm_tw hL) hB (hF.natCard hL) hg hgt hgu hgw hvt.1 hvt.2 hvtu

theorem alphaOf_eq_bot_of_shape (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hα : ∀ (M : Type) [Group M] [Finite M], IsSimpleGroup M →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel M .PSL 3 p f ∨ LieModel M .PSU 3 p f)) →
      ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
        ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
          (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥)
    (hL : TightLargeHypR r n Y R S t) (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hA : ¬ TriNbrAll R t) (hnc : ¬ DConnected (linkFam R t)) (htr : LinkTrans R t)
    (hcase : LinkWR R t ∨ LinkSR R t) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
  obtain ⟨hstar, hgen⟩ := star_frames_of_shape hL hA htr hnc hcase
  exact alphaOf_eq_bot_of_starFrames hL hc
    (fun _ _ _ _ hF => hyp51_starFrame_of_shape hr hNo h4 hα hL hcase hF) hstar hgen

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

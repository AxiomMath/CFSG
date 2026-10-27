module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitComp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp cjComp_one cjComp_mul mem_cjComp_iff
  mem_cjComp_of_mem layerMul_injective conj_eq_π π π_layerMul conj_mem_layer
  mem_centralizer_layer_of_forall π_mem)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x : Y}

@[expose] def conjCore (x : Y) (S : Subgroup Y) : Subgroup Y where
  carrier := {w | ∀ k : ℕ, (x ^ k)⁻¹ * w * x ^ k ∈ S}
  mul_mem' := fun {a b} ha hb k => by
    have := S.mul_mem (ha k) (hb k)
    rwa [show (x ^ k)⁻¹ * a * x ^ k * ((x ^ k)⁻¹ * b * x ^ k) = (x ^ k)⁻¹ * (a * b) * x ^ k by
      group] at this
  one_mem' := fun k => by simp
  inv_mem' := fun {a} ha k => by
    have := S.inv_mem (ha k)
    rwa [show ((x ^ k)⁻¹ * a * x ^ k)⁻¹ = (x ^ k)⁻¹ * a⁻¹ * x ^ k by group] at this

theorem conjCore_le (S : Subgroup Y) : conjCore x S ≤ S := fun w hw => by
  simpa using hw 0

theorem conj_mem_conjCore {S : Subgroup Y} (hx : x ^ p = 1) (hp : 0 < p) {w : Y}
    (hw : w ∈ conjCore x S) : x * w * x⁻¹ ∈ conjCore x S := by
  intro k
  cases k with
  | zero =>
    have h1 := hw (p - 1)
    have h2 : x ^ (p - 1) = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp, hx]
    rw [h2] at h1
    simpa using h1
  | succ k =>
    have h1 := hw k
    rwa [show (x ^ (k + 1))⁻¹ * (x * w * x⁻¹) * x ^ (k + 1) = (x ^ k)⁻¹ * w * x ^ k by
      rw [pow_succ']
      group]

@[expose] noncomputable def actHom (P : Subgroup Y) (L : ComponentIndex Y) :
    ↥(compKer P) →* MulAut ↥L.1 :=
  L.1.normalizerMonoidHom.comp
    (Subgroup.inclusion (fun _ hg => mem_normalizer_of_mem_compKer hg L))

theorem actHom_apply (L : ComponentIndex Y) (q : ↥(compKer P)) (c : ↥L.1) :
    (((actHom P L q) c : ↥L.1) : Y) = (q : Y) * (c : Y) * (q : Y)⁻¹ := rfl

@[expose] noncomputable def Qsub (P : Subgroup Y) (L : ComponentIndex Y)
    (R : Subgroup (MulAut ↥L.1)) : Subgroup Y :=
  (R.comap (actHom P L)).map (compKer P).subtype

theorem mem_Qsub {L : ComponentIndex Y} {R : Subgroup (MulAut ↥L.1)} {y : Y} :
    y ∈ Qsub P L R ↔ ∃ q : ↥(compKer P), actHom P L q ∈ R ∧ (q : Y) = y := by
  rw [Qsub, Subgroup.mem_map]
  simp only [Subgroup.mem_comap, Subgroup.coe_subtype]

theorem Qsub_le {L : ComponentIndex Y} {R : Subgroup (MulAut ↥L.1)} : Qsub P L R ≤ compKer P := by
  intro y hy
  obtain ⟨q, -, rfl⟩ := mem_Qsub.mp hy
  exact q.2

theorem actHom_layer (h : SplitCfg p P x) (L : ComponentIndex Y) {u : Y} (hu : u ∈ compKer P)
    (hul : u ∈ layer Y) : actHom P L ⟨u, hu⟩ ∈ inner ↥L.1 := by
  refine ⟨⟨π (hZ := h.centre) L u hul, π_mem L u hul⟩, ?_⟩
  refine MulEquiv.ext fun c => Subtype.ext ?_
  rw [actHom_apply]
  exact (conj_eq_π (hZ := h.centre) L hul c.2).symm

theorem actHom_eq_one_iff (L : ComponentIndex Y) (q : ↥(compKer P)) :
    actHom P L q = 1 ↔ ∀ c ∈ L.1, (q : Y) * c = c * (q : Y) := by
  constructor
  · intro h c hc
    have := congrArg (fun σ : MulAut ↥L.1 => ((σ ⟨c, hc⟩ : ↥L.1) : Y)) h
    simp only [actHom_apply, MulAut.one_apply] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  · intro h
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [actHom_apply]
    simp only [MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (h c c.2)

theorem mem_centralizer_layer_of_pow (h : SplitCfg p P x) (L0 : ComponentIndex Y) (g : Y)
    (hg : ∀ k : ℕ, ∀ c ∈ L0.1,
      ((x ^ k)⁻¹ * g * x ^ k) * c = c * ((x ^ k)⁻¹ * g * x ^ k)) :
    g ∈ centralizer (layer Y : Set Y) := by
  refine mem_centralizer_layer_of_forall g fun C c hc => ?_
  obtain ⟨k, rfl⟩ := h.trans L0 C
  have hc' := (mem_cjComp_iff (x ^ k) L0).1 hc
  have e1 : g * c = x ^ k * (((x ^ k)⁻¹ * g * x ^ k) * ((x ^ k)⁻¹ * c * x ^ k)) * (x ^ k)⁻¹ := by
    group
  have e2 : c * g = x ^ k * (((x ^ k)⁻¹ * c * x ^ k) * ((x ^ k)⁻¹ * g * x ^ k)) * (x ^ k)⁻¹ := by
    group
  rw [e1, e2, hg k _ hc']

theorem conj_layerMul (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥)
    (f : ∀ C : ComponentIndex Y, ↥C.1) (C : ComponentIndex Y) {c : Y} (hc : c ∈ C.1) :
    layerMul Y f * c * (layerMul Y f)⁻¹ = (f C : Y) * c * (f C : Y)⁻¹ := by
  have hl : layerMul Y f ∈ layer Y := by rw [← layerMul_range]; exact ⟨f, rfl⟩
  rw [conj_eq_π (hZ := hZ) C hl hc, π_layerMul (hZ := hZ) C f hl]

theorem exists_dec (h : SplitCfg p P x) (L0 : ComponentIndex Y) (R : Subgroup (MulAut ↥L0.1))
    (hdec : ∀ q : ↥(compKer P), ∃ a : ↥L0.1, (a : Y) ∈ P ∧ ∃ r ∈ R,
      actHom P L0 q = MulAut.conj a * r)
    {q : Y} (hq : q ∈ compKer P) :
    ∃ a ∈ P ⊓ layer Y, a⁻¹ * q ∈ conjCore x (Qsub P L0 R) := by
  letI := compAction Y
  obtain ⟨idx, hidx1, hidx2⟩ := exists_idx (G := Y) (Ω := ComponentIndex Y) h.prime h.card_comp
    h.x_pow (fun α β => h.trans α β) L0
  have hidx1' : ∀ C : ComponentIndex Y, cjComp (x ^ idx C) L0 = C := hidx1
  have hidx2' : ∀ k : ℕ, x ^ idx (cjComp (x ^ k) L0) = x ^ k := hidx2
  have hxk : ∀ k : ℕ, x ^ k ∈ P := fun k => P.pow_mem h.x_mem k
  have hxkinv : ∀ k : ℕ, (x ^ k)⁻¹ ∈ P := fun k => P.inv_mem (hxk k)
  have hqj : ∀ j : ℕ, (x ^ j)⁻¹ * q * x ^ j ∈ compKer P := fun j => by
    have := conj_mem_compKer (hxkinv j) hq
    rwa [inv_inv] at this
  choose b hbP r hrR hbr using fun C : ComponentIndex Y =>
    hdec ⟨(x ^ idx C)⁻¹ * q * x ^ idx C, hqj (idx C)⟩
  let f : ∀ C : ComponentIndex Y, ↥C.1 := fun C =>
    ⟨x ^ idx C * (b C : Y) * (x ^ idx C)⁻¹, by
      have := mem_cjComp_of_mem (x ^ idx C) L0 (b C).2
      rwa [hidx1' C] at this⟩
  have hfP : ∀ C : ComponentIndex Y, ((f C : ↥C.1) : Y) ∈ P := fun C =>
    P.mul_mem (P.mul_mem (hxk _) (hbP C)) (P.inv_mem (hxk _))
  obtain ⟨a, ha⟩ : ∃ a : Y, a = layerMul Y f := ⟨_, rfl⟩
  have haP : a ∈ P := by rw [ha]; exact layerMul_mem f hfP
  have hal : a ∈ layer Y := by rw [ha, ← layerMul_range]; exact ⟨f, rfl⟩
  have haC : ∀ (C : ComponentIndex Y) (c : Y), c ∈ C.1 →
      a * c * a⁻¹ = (f C : Y) * c * (f C : Y)⁻¹ := by
    intro C c hc
    rw [ha]
    exact conj_layerMul h.centre f C hc
  refine ⟨a, ⟨haP, hal⟩, fun k => ?_⟩
  have hj := hidx2' k
  set Ck : ComponentIndex Y := cjComp (x ^ k) L0 with hCk
  have hfC : (f Ck : Y) = x ^ k * (b Ck : Y) * (x ^ k)⁻¹ := by
    show x ^ idx Ck * (b Ck : Y) * (x ^ idx Ck)⁻¹ = _
    rw [hj]
  have hu : (x ^ k)⁻¹ * a * x ^ k ∈ compKer P := by
    apply layer_inf_le_compKer
    refine ⟨P.mul_mem (P.mul_mem (hxkinv k) haP) (hxk k), ?_⟩
    have := conj_mem_layer (x ^ k)⁻¹ hal
    rwa [inv_inv] at this
  have hqk : (x ^ k)⁻¹ * q * x ^ k ∈ compKer P := hqj k
  have hact_u : actHom P L0 ⟨(x ^ k)⁻¹ * a * x ^ k, hu⟩ = MulAut.conj (b Ck) := by
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [actHom_apply, MulAut.conj_apply]
    have hc' : x ^ k * (c : Y) * (x ^ k)⁻¹ ∈ Ck.1 := mem_cjComp_of_mem (x ^ k) L0 c.2
    have e := haC Ck _ hc'
    rw [hfC] at e
    show _ = (b Ck : Y) * (c : Y) * (b Ck : Y)⁻¹
    calc ((x ^ k)⁻¹ * a * x ^ k) * (c : Y) * ((x ^ k)⁻¹ * a * x ^ k)⁻¹
        = (x ^ k)⁻¹ * (a * (x ^ k * (c : Y) * (x ^ k)⁻¹) * a⁻¹) * x ^ k := by group
      _ = (x ^ k)⁻¹ * ((x ^ k * (b Ck : Y) * (x ^ k)⁻¹) * (x ^ k * (c : Y) * (x ^ k)⁻¹) *
            (x ^ k * (b Ck : Y) * (x ^ k)⁻¹)⁻¹) * x ^ k := by rw [e]
      _ = (b Ck : Y) * (c : Y) * (b Ck : Y)⁻¹ := by group
  have hact_q : actHom P L0 ⟨(x ^ k)⁻¹ * q * x ^ k, hqk⟩ = MulAut.conj (b Ck) * r Ck := by
    have e2 : (⟨(x ^ k)⁻¹ * q * x ^ k, hqk⟩ : ↥(compKer P)) =
        ⟨(x ^ idx Ck)⁻¹ * q * x ^ idx Ck, hqj (idx Ck)⟩ :=
      Subtype.ext (show (x ^ k)⁻¹ * q * x ^ k = (x ^ idx Ck)⁻¹ * q * x ^ idx Ck by rw [hj])
    rw [e2]
    exact hbr Ck
  refine mem_Qsub.mpr ⟨(⟨(x ^ k)⁻¹ * a * x ^ k, hu⟩ : ↥(compKer P))⁻¹ *
    ⟨(x ^ k)⁻¹ * q * x ^ k, hqk⟩, ?_, ?_⟩
  · rw [map_mul, map_inv, hact_u, hact_q, inv_mul_cancel_left]
    exact hrR Ck
  · show ((x ^ k)⁻¹ * a * x ^ k)⁻¹ * ((x ^ k)⁻¹ * q * x ^ k) = (x ^ k)⁻¹ * (a⁻¹ * q) * x ^ k
    group

theorem inf_conjCore_eq_bot (h : SplitCfg p P x) (L0 : ComponentIndex Y)
    (R : Subgroup (MulAut ↥L0.1)) (hR : R ⊓ inner ↥L0.1 = ⊥) {a : Y} (ha : a ∈ P ⊓ layer Y)
    (haW : a ∈ conjCore x (Qsub P L0 R)) : a = 1 := by
  refine h.cent a ha.1 (mem_centralizer_layer_of_pow h L0 a fun k c hc => ?_)
  obtain ⟨q, hqR, hqe⟩ := mem_Qsub.mp (haW k)
  have hl : (x ^ k)⁻¹ * a * x ^ k ∈ layer Y := by
    have := conj_mem_layer (x ^ k)⁻¹ ha.2
    rwa [inv_inv] at this
  have hinner : actHom P L0 q ∈ inner ↥L0.1 :=
    actHom_layer h L0 q.2 (by rw [hqe]; exact hl)
  have h1 : actHom P L0 q ∈ R ⊓ inner ↥L0.1 := ⟨hqR, hinner⟩
  rw [hR, Subgroup.mem_bot] at h1
  have h2 := (actHom_eq_one_iff L0 q).1 h1 c hc
  rwa [hqe] at h2

theorem commute_conjCore (h : SplitCfg p P x) (L0 : ComponentIndex Y)
    (R : Subgroup (MulAut ↥L0.1)) (hRc : IsCyclic R) {w w' : Y}
    (hw : w ∈ conjCore x (Qsub P L0 R)) (hw' : w' ∈ conjCore x (Qsub P L0 R)) :
    w * w' = w' * w := by
  have hwP : w ∈ P := compKer_le (Qsub_le (conjCore_le _ hw))
  have hw'P : w' ∈ P := compKer_le (Qsub_le (conjCore_le _ hw'))
  have hc1 : w * w' * w⁻¹ * w'⁻¹ = 1 := by
    refine h.cent _ (P.mul_mem (P.mul_mem (P.mul_mem hwP hw'P) (P.inv_mem hwP)) (P.inv_mem hw'P))
      (mem_centralizer_layer_of_pow h L0 _ fun k c0 hc0 => ?_)
    obtain ⟨qw, hqwR, hqwe⟩ := mem_Qsub.mp (hw k)
    obtain ⟨qw', hqw'R, hqw'e⟩ := mem_Qsub.mp (hw' k)
    have hcomm : actHom P L0 qw * actHom P L0 qw' = actHom P L0 qw' * actHom P L0 qw := by
      have := mul_comm' (⟨actHom P L0 qw, hqwR⟩ : ↥R) ⟨actHom P L0 qw', hqw'R⟩
      exact congrArg Subtype.val this
    have h1 : actHom P L0 (qw * qw' * qw⁻¹ * qw'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have h2 := (actHom_eq_one_iff L0 _).1 h1 c0 hc0
    have e : ((qw * qw' * qw⁻¹ * qw'⁻¹ : ↥(compKer P)) : Y) =
        (x ^ k)⁻¹ * (w * w' * w⁻¹ * w'⁻¹) * x ^ k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hqwe, hqw'e]
      group
    rwa [e] at h2
  have := congrArg (· * (w' * w)) hc1
  simp only [one_mul] at this
  rw [← this]
  group

theorem exists_complement (hsplit : KFactSylowSplit) (h7131 : GL83.I_7_13_1) (h : SplitCfg p P x) :
    ∃ W : Subgroup Y, W ≤ compKer P ∧ (∀ w ∈ W, x * w * x⁻¹ ∈ W) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧ (∀ a ∈ P ⊓ layer Y, a ∈ W → a = 1) ∧
      ∀ q ∈ compKer P, ∃ a ∈ P ⊓ layer Y, ∃ w ∈ W, q = a * w := by
  have hp := h.prime
  obtain ⟨L0⟩ : Nonempty (ComponentIndex Y) :=
    Finite.card_pos_iff.mp (by rw [h.card_comp]; exact hp.pos)
  obtain ⟨hsimple, hnonab⟩ := simple_comp h L0
  obtain ⟨T, hTeq, -⟩ := exists_sylow_comp h L0
  have hQp : IsPGroup p ↥(compKer P) := h.sylow.isPGroup.to_le compKer_le
  have hTmem : ∀ a ∈ T, (a : Y) ∈ P ⊓ L0.1 := by
    intro a ha
    have ha' : a ∈ (T : Subgroup ↥L0.1) := ha
    rw [hTeq] at ha'
    exact Subgroup.mem_subgroupOf.mp ha'
  have hT : ∀ a ∈ T, ∃ q : ↥(compKer P), actHom P L0 q = MulAut.conj a := by
    intro a ha
    have hamem := hTmem a ha
    have hq : (a : Y) ∈ compKer P :=
      layer_inf_le_compKer ⟨hamem.1, component_le_layer L0.2 hamem.2⟩
    refine ⟨⟨a, hq⟩, MulEquiv.ext fun c => Subtype.ext ?_⟩
    rw [actHom_apply, MulAut.conj_apply]
    rfl
  obtain ⟨R, hRc, hRi, hdec⟩ := local_split hsplit h7131 hp
    (by have := h.five_le; omega) hsimple hnonab (catalog_comp h L0) (pRank_comp_le_one h L0) hQp
    (actHom P L0) T hT
  have hdec' : ∀ q : ↥(compKer P), ∃ a : ↥L0.1, (a : Y) ∈ P ∧ ∃ r ∈ R,
      actHom P L0 q = MulAut.conj a * r := by
    intro q
    obtain ⟨a, haT, r, hr, e⟩ := hdec q
    exact ⟨a, (hTmem a haT).1, r, hr, e⟩
  refine ⟨conjCore x (Qsub P L0 R), (conjCore_le _).trans Qsub_le,
    fun w hw => conj_mem_conjCore h.x_pow hp.pos hw,
    fun w hw w' hw' => commute_conjCore h L0 R hRc hw hw',
    fun a ha haW => inf_conjCore_eq_bot h L0 R hRi ha haW, fun q hq => ?_⟩
  obtain ⟨a, ha, hw⟩ := exists_dec h L0 R hdec' hq
  exact ⟨a, ha, a⁻¹ * q, hw, by group⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

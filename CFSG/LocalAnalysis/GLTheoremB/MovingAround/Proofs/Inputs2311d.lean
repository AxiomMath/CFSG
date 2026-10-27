module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c2
public import CFSG.LieType.SeitzGeneration.SpFourScope
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagInndiagGen
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagRegular
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisClassSplit
import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Main
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainRows
public import CFSG.LieType.SeitzGeneration.ExcSeitzWide
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.LieType.SeitzGeneration.SpPlaneBlocksThree
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration.SpPlaneThree

section SpUni

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_spTransvection_pow (u : Fin r ⊕ Fin r → K) (t : K) (n : ℕ) (y : Fin r ⊕ Fin r → K) :
    spEnd (spTransvection u t ^ n) y = y + ((n : K) * t * spForm r K y u) • u := by
  induction n generalizing y with
  | zero => simp [spEnd_one]
  | succ n ih =>
    rw [pow_succ, spEnd_mul, Module.End.mul_apply, ih, spEnd_spTransvection, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, spForm_isAlt u, smul_eq_mul, mul_zero, add_zero]
    push_cast
    module

theorem spTransvection_pow_ringChar (u : Fin r ⊕ Fin r → K) (t : K) :
    spTransvection u t ^ ringChar K = 1 := by
  refine eq_one_of_spEnd_fix fun y => ?_
  rw [spEnd_spTransvection_pow, ringChar.Nat.cast_ringChar, zero_mul, zero_mul, zero_smul, add_zero]

theorem mixElt_pow_ringChar {z : StatedSp r K} (hz : z ^ 3 = 1) {u : Fin r ⊕ Fin r → K}
    (hu : spForm r K u (spEnd z u) = 0) (c : K) : mixElt z u c ^ ringChar K = 1 := by
  obtain ⟨h13, h23⟩ := mixElt_orth hz hu
  have k12 : Commute (spTransvection u c) (spTransvection (spEnd z u) c) :=
    spTransvection_comm_of_form_eq_zero hu c c
  have k13 : Commute (spTransvection u c) (spTransvection (spEnd z (spEnd z u)) c) :=
    spTransvection_comm_of_form_eq_zero h13 c c
  have k23 : Commute (spTransvection (spEnd z u) c) (spTransvection (spEnd z (spEnd z u)) c) :=
    spTransvection_comm_of_form_eq_zero h23 c c
  unfold mixElt
  rw [(k13.mul_left k23).mul_pow, k12.mul_pow, spTransvection_pow_ringChar, spTransvection_pow_ringChar,
    spTransvection_pow_ringChar, one_mul, one_mul]

@[expose] def spUniSpan (E : Subgroup (StatedSp r K)) : Subgroup (StatedSp r K) :=
  Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1}

theorem transCenter_uni_of_fixed {E : Subgroup (StatedSp r K)} {x : StatedSp r K} (hxE : x ∈ E)
    (hx1 : x ≠ 1) {u : Fin r ⊕ Fin r → K} (hu : spEnd x u = u) : TransCenter (spUniSpan E) u :=
  fun t => Subgroup.subset_closure ⟨x, hxE, hx1, commute_spTransvection hu t, spTransvection_pow_ringChar u t⟩

end SpUni

section SpFour

variable {K : Type} [Field K]

theorem mixed_center_of_isotropic_uni {H : Subgroup (StatedSp 2 K)} {z : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (D : MixData ⊤ z P₀ P₁)
    (hc₀ : ∀ v ∈ P₀, TransCenter H v) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {u₀ u₁ : Fin 2 ⊕ Fin 2 → K}
    (hu₀ : u₀ ∈ P₀) (hu₁ : u₁ ∈ P₁) (hiso : spForm 2 K (u₀ + u₁) (spEnd z (u₀ + u₁)) = 0)
    (hmix : ∀ c, mixElt z (u₀ + u₁) c ∈ H)
    (hstar : ∃ v ∈ P₀, spForm 2 K v u₀ • u₁ + spForm 2 K v (spEnd z u₀) • spEnd z u₁ +
      spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₁) ≠ 0) :
    ∃ y₀ ∈ P₀, ∃ y₁ ∈ P₁, y₀ ≠ 0 ∧ y₁ ≠ 0 ∧ TransCenter H (y₀ + y₁) := by
  obtain ⟨v, hv, hB⟩ := hstar
  obtain ⟨c₂, hc₂0, hc₂1⟩ := hK
  have hZ₀ : spEnd z u₀ ∈ P₀ := D.stab₀ u₀ hu₀
  have hZZ₀ : spEnd z (spEnd z u₀) ∈ P₀ := D.stab₀ _ hZ₀
  have hZ₁ : spEnd z u₁ ∈ P₁ := D.stab₁ u₁ hu₁
  have hZZ₁ : spEnd z (spEnd z u₁) ∈ P₁ := D.stab₁ _ hZ₁
  obtain ⟨A, hA⟩ : ∃ A : Fin 2 ⊕ Fin 2 → K, A = spForm 2 K v u₀ • u₀ +
      spForm 2 K v (spEnd z u₀) • spEnd z u₀ +
      spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₀) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : Fin 2 ⊕ Fin 2 → K, B = spForm 2 K v u₀ • u₁ +
      spForm 2 K v (spEnd z u₀) • spEnd z u₁ +
      spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₁) := ⟨_, rfl⟩
  have hAmem : A ∈ P₀ := by
    rw [hA]
    exact P₀.add_mem (P₀.add_mem (P₀.smul_mem _ hu₀) (P₀.smul_mem _ hZ₀)) (P₀.smul_mem _ hZZ₀)
  have hBmem : B ∈ P₁ := by
    rw [hBd]
    exact P₁.add_mem (P₁.add_mem (P₁.smul_mem _ hu₁) (P₁.smul_mem _ hZ₁)) (P₁.smul_mem _ hZZ₁)
  have hB0 : B ≠ 0 := by rw [hBd]; exact hB
  have z0 : spForm 2 K v u₁ = 0 := D.orth v hv _ hu₁
  have z1 : spForm 2 K v (spEnd z u₁) = 0 := D.orth v hv _ hZ₁
  have z2 : spForm 2 K v (spEnd z (spEnd z u₁)) = 0 := D.orth v hv _ hZZ₁
  have key : ∀ c : K, spEnd (mixElt z (u₀ + u₁) c) v = (v + c • A) + c • B := by
    intro c
    rw [spEnd_mixElt D.cube hiso c v, hA, hBd]
    simp only [map_add, z0, z1, z2, add_zero]
    module
  have hy₀ : ∃ c : K, c ≠ 0 ∧ v + c • A ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : v + (1 : K) • A = 0 := hcon 1 one_ne_zero
    have h2 : v + c₂ • A = 0 := hcon c₂ hc₂0
    have h3 : (1 - c₂) • A = 0 := by linear_combination (norm := module) h1 - h2
    have hA0 : A = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.2 (Ne.symm hc₂1))
    have hv0 : v = 0 := by
      rw [hA0, smul_zero, add_zero] at h1
      exact h1
    apply hB0
    rw [hBd, hv0]
    simp
  obtain ⟨c, hc0, hy₀⟩ := hy₀
  refine ⟨v + c • A, P₀.add_mem hv (P₀.smul_mem c hAmem), c • B, P₁.smul_mem c hBmem, hy₀,
    smul_ne_zero hc0 hB0, ?_⟩
  have := (hc₀ v hv).map (hmix c)
  rwa [key c] at this

theorem exists_mixed_center_uni [Finite K] {H : Subgroup (StatedSp 2 K)} {z : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (D : MixData ⊤ z P₀ P₁) (hc₀ : ∀ v ∈ P₀, TransCenter H v)
    (hmix : ∀ u, spForm 2 K u (spEnd z u) = 0 → ∀ c, mixElt z u c ∈ H) :
    ∃ y₀ ∈ P₀, ∃ y₁ ∈ P₁, y₀ ≠ 0 ∧ y₁ ≠ 0 ∧ TransCenter H (y₀ + y₁) := by
  by_cases hsp : ∃ l : K, l ^ 2 + l + 1 = 0
  · obtain ⟨l, hl⟩ := hsp
    obtain ⟨u₀, hu₀, u₁, hu₁, hiso, hstar⟩ := exists_isotropic_split h3 D hl
    exact mixed_center_of_isotropic_uni D hc₀ hK hu₀ hu₁ hiso (hmix _ hiso) hstar
  · push Not at hsp
    obtain ⟨u₀, hu₀, u₁, hu₁, hiso, hstar⟩ := exists_isotropic_nonsplit h3 D hsp
    exact mixed_center_of_isotropic_uni D hc₀ hK hu₀ hu₁ hiso (hmix _ hiso) hstar

theorem uniClosure_of_planeBlocks [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {E : Subgroup (StatedSp 2 K)} {a b : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (B : PlaneBlocks E a b P₀ P₁) : spUniSpan E = ⊤ := by
  set H : Subgroup (StatedSp 2 K) := spUniSpan E with hH
  have hC₁ : ∀ v ∈ P₁, TransCenter H v := fun v hv => transCenter_uni_of_fixed B.ha B.ha1 (B.fix_a v hv)
  have hC₀ : ∀ v ∈ P₀, TransCenter H v := fun v hv => transCenter_uni_of_fixed B.hb B.hb1 (B.fix_b v hv)
  have hab : a * b ∈ E := E.mul_mem B.ha B.hb
  have hab1 : a * b ≠ 1 := by
    intro h
    apply B.ha1
    refine eq_one_of_spEnd_fix fun v => ?_
    have hv : v ∈ P₀ ⊔ P₁ := by rw [B.sup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hv
    have h1 : spEnd (a * b) p = p := by rw [h, spEnd_one_apply]
    rw [spEnd_comp_apply, B.fix_b p hp] at h1
    rw [map_add, h1, B.fix_a p' hp']
  have hcube : (a * b) ^ 3 = 1 := by
    have hc : Commute a b := hcomm a B.ha b B.hb
    rw [hc.mul_pow, hexp a B.ha, hexp b B.hb, one_mul]
  have D : MixData ⊤ (a * b) P₀ P₁ :=
    { cube := hcube
      central := fun _ _ => Subgroup.mem_top _
      center₀ := fun _ _ _ => Subgroup.mem_top _
      sup := B.sup
      orth := B.orth
      nd₀ := B.nd₀
      nd₁ := B.nd₁
      rank₀ := B.rank₀
      rank₁ := B.rank₁
      stab₀ := fun v hv => by
        rw [spEnd_comp_apply, B.fix_b v hv]
        exact B.stab_a₀ v hv
      stab₁ := fun v hv => by
        rw [spEnd_comp_apply, B.fix_a _ (B.stab_b₁ v hv)]
        exact B.stab_b₁ v hv
      norm₀ := fun v hv => by
        have h1 : spEnd (a * b) v = spEnd a v := by rw [spEnd_comp_apply, B.fix_b v hv]
        have h2 : spEnd (a * b) (spEnd a v) = spEnd a (spEnd a v) := by
          rw [spEnd_comp_apply, B.fix_b _ (B.stab_a₀ v hv)]
        rw [h1, h2]
        exact B.norm_a v hv
      norm₁ := fun v hv => by
        have h1 : spEnd (a * b) v = spEnd b v := by
          rw [spEnd_comp_apply, B.fix_a _ (B.stab_b₁ v hv)]
        have h2 : spEnd (a * b) (spEnd b v) = spEnd b (spEnd b v) := by
          rw [spEnd_comp_apply, B.fix_a _ (B.stab_b₁ _ (B.stab_b₁ v hv))]
        rw [h1, h2]
        exact B.norm_b v hv }
  have hmix : ∀ u, spForm 2 K u (spEnd (a * b) u) = 0 → ∀ c, mixElt (a * b) u c ∈ H := fun u hu c =>
    Subgroup.subset_closure ⟨a * b, hab, hab1, mixElt_comm hcube hu c, mixElt_pow_ringChar hcube hu c⟩
  obtain ⟨y₀, hy₀, y₁, hy₁, hy₀0, hy₁0, hc⟩ := exists_mixed_center_uni h3 hK D hC₀ hmix
  have hmix' : ∀ y₀' ∈ P₀, ∀ y₁' ∈ P₁, y₀' ≠ 0 → y₁' ≠ 0 → TransCenter H (y₀' + y₁') := by
    intro y₀' hy₀' y₁' hy₁' h0 h1
    have o₀₁ : ∀ x ∈ P₁, ∀ c ∈ P₀, spForm 2 K x c = 0 := fun x hx c hc => by
      rw [← spForm_isAlt.neg_eq c x, B.orth c hc x hx, neg_zero]
    obtain ⟨g₀, hg₀, hg₀y, hg₀fix⟩ := exists_mem_fixing_eq (U := P₀) B.nd₀ hC₀ hy₀ hy₀' hy₀0 h0
    obtain ⟨g₁, hg₁, hg₁y, hg₁fix⟩ := exists_mem_fixing_eq (U := P₁) B.nd₁ hC₁ hy₁ hy₁' hy₁0 h1
    have e₀ : spEnd g₀ y₁ = y₁ := hg₀fix y₁ (o₀₁ y₁ hy₁)
    have e₁ : spEnd g₁ y₀' = y₀' := hg₁fix y₀' (B.orth y₀' hy₀')
    have := hc.map (H.mul_mem hg₁ hg₀)
    rwa [spEnd_comp_apply, map_add, hg₀y, e₀, map_add, e₁, hg₁y] at this
  have hspan : ⨆ i, ![P₀, P₁] i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ P₀ ⊔ P₁ := by rw [B.sup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem (0 : Fin 2) hp)
      (Submodule.mem_iSup_of_mem (1 : Fin 2) hp')
  have hall : ∀ v, TransCenter H v := by
    refine transCenter_of_pairs (Vs := ![P₀, P₁]) hspan ?_ ?_ ?_ ?_
    · intro i j hij u hu v hv
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact B.orth u hu v hv
      · rw [← spForm_isAlt.neg_eq v u, B.orth v hv u hu, neg_zero]
      · exact absurd rfl hij
    · intro i
      fin_cases i
      · exact B.nd₀
      · exact B.nd₁
    · intro i c hc
      fin_cases i
      · exact hC₀ c hc
      · exact hC₁ c hc
    · intro i j hij y hy y' hy' hy0 hy'0
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hmix' y hy y' hy' hy0 hy'0
      · rw [add_comm]
        exact hmix' y' hy' y hy hy'0 hy0
      · exact absurd rfl hij
  exact eq_top_of_transCenter hall

theorem uniClosure_spFour_three [Finite K] (h3 : (3 : K) ≠ 0) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    {E : Subgroup (StatedSp 2 K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) : spUniSpan E = ⊤ := by
  obtain ⟨a, b, P₀, P₁, B⟩ := exists_planeBlocks h3 hcomm hexp hcard
  exact uniClosure_of_planeBlocks h3 hK hcomm hexp B

end SpFour

section SpPlane

variable {r : ℕ} {K : Type} [Field K]

theorem transCenter_of_four_uni [Finite K] (h3 : (3 : K) ≠ 0) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hnd : ((spForm r K).restrict W).Nondegenerate)
    (hdim : Module.finrank K W = 4) (hstab : E ≤ spStab W)
    (hfaith : ∀ x ∈ E, (∀ v ∈ W, spEnd x v = v) → x = 1) {v : Fin r ⊕ Fin r → K} (hv : v ∈ W) :
    TransCenter (spUniSpan E) v := by
  obtain ⟨m, e, heU, hm⟩ := SpSubEmb.exists hnd
  have hm2 : m = 2 := by omega
  subst hm2
  have hstab' : E ≤ spStab e.U := heU ▸ hstab
  set ψ : E →* StatedSp 2 K := e.res.comp (Subgroup.inclusion hstab') with hψ
  have hψa : ∀ a : E, ψ a = e.res ⟨a, hstab' a.2⟩ := fun a => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hψa, e.res_eq_one_iff] at hx
    exact Subtype.ext (hfaith x x.2 fun w hw => hx w (heU ▸ hw))
  have hrange : Nat.card ψ.range = 9 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrangeComm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hcomm a a.2 b b.2))
  have hrangeExp : ∀ x ∈ ψ.range, x ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hexp a a.2)
    rw [this, map_one]
  have hplane := uniClosure_spFour_three h3 hK hrangeComm hrangeExp hrange
  have hle : e.ext.range ≤ spUniSpan E := by
    have key : e.ext.range = Subgroup.closure (e.ext ''
        {g | ∃ x ∈ ψ.range, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1}) := by
      rw [MonoidHom.range_eq_map, ← MonoidHom.map_closure]
      congr 1
      exact hplane.symm
    rw [key, Subgroup.closure_le]
    rintro _ ⟨g, ⟨_, ⟨a, rfl⟩, hx1, hgx, hgr⟩, rfl⟩
    refine Subgroup.subset_closure ⟨(a : StatedSp r K), a.2, ?_,
      (e.commute_ext ⟨a, hstab' a.2⟩ hgx.symm).symm, by rw [← map_pow, hgr, map_one]⟩
    intro ha1
    apply hx1
    have : a = 1 := Subtype.ext ha1
    rw [this, map_one]
  intro t
  rw [← heU] at hv
  obtain ⟨x, hx⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = v := ⟨e.φ.symm ⟨v, hv⟩, by simp⟩
  rw [← hx, ← e.ext_spTransvection]
  exact hle ⟨_, rfl⟩

theorem exists_mixed_transCenter_uni [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E) {L N : Subgroup ↥E} (hL : Nat.card L = 3)
    (hN : Nat.card N = 3) (hLN : L ≠ N) (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) :
    ∃ u ∈ spLineSpace L, ∃ w ∈ spLineSpace N, u ≠ 0 ∧ w ≠ 0 ∧
      TransCenter (spUniSpan E) (u + w) := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hNL : N ≠ L := fun h => hLN h.symm
  obtain ⟨a, haL, ha1⟩ := exists_ne_one_of_one_lt_card (M := L) (by rw [hL]; norm_num)
  obtain ⟨b, hbN, hb1⟩ := exists_ne_one_of_one_lt_card (M := N) (by rw [hN]; norm_num)
  have ha1' : (a : StatedSp r K) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : StatedSp r K) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have ha3 : (a : StatedSp r K) ^ 3 = 1 := hexp a a.2
  have hb3 : (b : StatedSp r K) ^ 3 = 1 := hexp b b.2
  have hstabL : ∀ v ∈ spLineSpace L, spEnd (b : StatedSp r K) v ∈ spLineSpace L :=
    fun v hv => spLineSpace_stable_of_comm hcomm b hv
  have hstabN : ∀ v ∈ spLineSpace N, spEnd (a : StatedSp r K) v ∈ spLineSpace N :=
    fun v hv => spLineSpace_stable_of_comm hcomm a hv
  have hfixL : ∀ v ∈ spLineSpace L, spEnd (b : StatedSp r K) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hL hN hLN b.2 hbN hb1' hv h
  have hfixN : ∀ v ∈ spLineSpace N, spEnd (a : StatedSp r K) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hN hL hNL a.2 haL ha1' hv h
  obtain ⟨u, huL, hu⟩ := exists_spForm_ne_zero_of_no_fixed (U := spLineSpace L)
    (D.nondeg (some ⟨L, hL⟩)) hb3 hstabL hfixL hVL
  obtain ⟨w, hwN, hw⟩ := exists_spForm_ne_zero_of_no_fixed (U := spLineSpace N)
    (D.nondeg (some ⟨N, hN⟩)) ha3 hstabN hfixN hVN
  have hnu := norm_eq_zero_of_no_fixed hb3 hstabL hfixL huL
  have hnw := norm_eq_zero_of_no_fixed ha3 hstabN hfixN hwN
  have hbuL := hstabL u huL
  have hawN := hstabN w hwN
  set P : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K {u, spEnd (b : StatedSp r K) u}
    with hP
  set Q : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K {w, spEnd (a : StatedSp r K) w}
    with hQ
  have hPL : P ≤ spLineSpace L := Submodule.span_le.2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [huL, hbuL])
  have hQN : Q ≤ spLineSpace N := Submodule.span_le.2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hwN, hawN])
  have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥E // Nat.card M = 3}) ≠ some ⟨N, hN⟩ :=
    fun h => hLN (congrArg Subtype.val (Option.some.inj h))
  have horth : ∀ x ∈ P, ∀ y ∈ Q, spForm r K x y = 0 := fun x hx y hy =>
    D.orth _ _ hne x (hPL hx) y (hQN hy)
  have horth' : ∀ y ∈ Q, ∀ x ∈ P, spForm r K y x = 0 := fun y hy x hx => by
    rw [← spForm_isAlt.neg_eq x y, horth x hx y hy, neg_zero]
  have hWnd : ((spForm r K).restrict (P ⊔ Q)).Nondegenerate :=
    nondegenerate_sup_of_orthogonal (nondegenerate_span_pair hu) (nondegenerate_span_pair hw)
      horth horth'
  have hdisj : Disjoint P Q := (D.disjoint_lineSpace hL hN hLN).mono hPL hQN
  have hdim : Module.finrank K (P ⊔ Q : Submodule K _) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [disjoint_iff.mp hdisj, finrank_bot, hP, hQ, finrank_span_pair_of_spForm hu,
      finrank_span_pair_of_spForm hw] at h
    omega
  have haW : ∀ v ∈ P ⊔ Q, spEnd (a : StatedSp r K) v ∈ P ⊔ Q := by
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, spEnd_eq_of_mem_spLineSpace haL (hPL hx)]
    exact Submodule.add_mem_sup hx (span_pair_stable hnw y hy)
  have hbW : ∀ v ∈ P ⊔ Q, spEnd (b : StatedSp r K) v ∈ P ⊔ Q := by
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, spEnd_eq_of_mem_spLineSpace hbN (hQN hy)]
    exact Submodule.add_mem_sup (span_pair_stable hnu x hx) hy
  have hcommab : Commute (a : StatedSp r K) b := hcomm a a.2 b b.2
  have hind : (b : StatedSp r K) ∉ Subgroup.zpowers (a : StatedSp r K) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hbL : b ∈ L := by
      have : b = a ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [this]
      exact L.zpow_mem haL k
    have : b ∈ L ⊓ N := ⟨hbL, hbN⟩
    rw [inf_eq_bot_of_card_prime Nat.prime_three hL hN hLN, Subgroup.mem_bot] at this
    exact hb1 this
  have hao : orderOf (a : StatedSp r K) = 3 := orderOf_eq_prime ha3 ha1'
  have hbo : orderOf (b : StatedSp r K) = 3 := orderOf_eq_prime hb3 hb1'
  have hEeq : Subgroup.closure ({(a : StatedSp r K), (b : StatedSp r K)} : Set (StatedSp r K)) =
      E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      exacts [a.2, b.2]
    · rw [card_closure_pair' Nat.prime_three hcommab hao hbo hind, hcard]
      norm_num
  have hstabE : E ≤ spStab (P ⊔ Q) := by
    rw [← hEeq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mem_spStab_of_stable ha3 haW
    · exact mem_spStab_of_stable hb3 hbW
  have huW : u ∈ P ⊔ Q := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert _ _))
  have hwW : w ∈ P ⊔ Q := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  have hfaith : ∀ x ∈ E, (∀ v ∈ P ⊔ Q, spEnd x v = v) → x = 1 := by
    intro x hxE hx
    by_contra hx1
    have hx1' : (⟨x, hxE⟩ : ↥E) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hx3 : (⟨x, hxE⟩ : ↥E) ^ 3 = 1 := Subtype.ext (hexp x hxE)
    have hXcard : Nat.card (Subgroup.zpowers (⟨x, hxE⟩ : ↥E)) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hx3 hx1'
    have hxX : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.zpowers (⟨x, hxE⟩ : ↥E) := Subgroup.mem_zpowers _
    by_cases hXL : Subgroup.zpowers (⟨x, hxE⟩ : ↥E) = L
    · have hxL : (⟨x, hxE⟩ : ↥E) ∈ L := hXL ▸ hxX
      have hw0 : w = 0 := D.eq_zero_of_fixed_spLineSpace hN hL hNL hxE hxL hx1 hwN (hx w hwW)
      exact hw (by rw [hw0, map_zero, LinearMap.zero_apply])
    · have hu0 : u = 0 := D.eq_zero_of_fixed_spLineSpace hL hXcard (Ne.symm hXL) hxE hxX hx1 huL
        (hx u huW)
      exact hu (by rw [hu0, map_zero, LinearMap.zero_apply])
  refine ⟨u, huL, w, hwN, fun h => hu (by rw [h, map_zero, LinearMap.zero_apply]),
    fun h => hw (by rw [h, map_zero, LinearMap.zero_apply]), ?_⟩
  exact transCenter_of_four_uni h3 hK hcomm hexp hcard hWnd hdim hstabE hfaith
    (Submodule.add_mem _ huW hwW)

theorem transCenter_of_mem_summand_three_uni {E : Subgroup (StatedSp r K)} (hcard : Nat.card E = 9)
    (i : Option {M : Subgroup ↥E // Nat.card M = 3}) {c : Fin r ⊕ Fin r → K}
    (hc : c ∈ spInnerSummand 3 E i) : TransCenter (spUniSpan E) c := by
  rcases i with _ | ⟨M, hM⟩
  · obtain ⟨t, htE, ht1⟩ := exists_ne_one_of_one_lt_card (M := E) (by rw [hcard]; norm_num)
    exact transCenter_uni_of_fixed htE ht1
      (CFSG.RankThree.Classical.mem_fixSub.mp hc ⟨t, htE⟩ (Subgroup.mem_top _))
  · obtain ⟨t, htM, ht1⟩ := exists_ne_one_of_one_lt_card (M := M) (by rw [hM]; norm_num)
    exact transCenter_uni_of_fixed t.2 (fun h => ht1 (Subtype.ext h))
      (spEnd_eq_of_mem_spLineSpace htM hc)

theorem transCenter_add_of_mem_summands_three_uni {E : Subgroup (StatedSp r K)}
    (D : SpPlaneDecomp 3 E) {M : Subgroup ↥E} (hM : Nat.card M = 3) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spPlaneFix E) (hy' : y' ∈ spLineSpace M) :
    TransCenter (spUniSpan E) (y + y') := by
  obtain ⟨t, htM, ht1⟩ := exists_ne_one_of_one_lt_card (M := M) (by rw [hM]; norm_num)
  have hker := D.ker_eq M hM t htM ht1
  have hmem : y + y' ∈ spLineFix M := by
    rw [hker.2]
    exact Submodule.add_mem_sup hy hy'
  rw [← hker.1] at hmem
  exact transCenter_uni_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hmem)

theorem transCenter_pair_three_uni [Finite K] (h3 : (3 : K) ≠ 0) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E)
    (i j : Option {M : Subgroup ↥E // Nat.card M = 3}) (hij : i ≠ j) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spInnerSummand 3 E i) (hy' : y' ∈ spInnerSummand 3 E j) (hy0 : y ≠ 0)
    (hy'0 : y' ≠ 0) : TransCenter (spUniSpan E) (y + y') := by
  classical
  rcases i with _ | ⟨L, hL⟩ <;> rcases j with _ | ⟨N, hN⟩
  · exact absurd rfl hij
  · exact transCenter_add_of_mem_summands_three_uni D hN hy hy'
  · rw [add_comm]
    exact transCenter_add_of_mem_summands_three_uni D hL hy' hy
  · have hLN : L ≠ N := fun h' => hij (by subst h'; rfl)
    have hVL : spLineSpace L ≠ ⊥ := fun h' => hy0 (by
      have : y ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy
      exact (Submodule.mem_bot K).mp this)
    have hVN : spLineSpace N ≠ ⊥ := fun h' => hy'0 (by
      have : y' ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy'
      exact (Submodule.mem_bot K).mp this)
    obtain ⟨u₀, hu₀, w₀, hw₀, hu₀0, hw₀0, hmix⟩ :=
      exists_mixed_transCenter_uni h3 hK hcomm hexp hcard D hL hN hLN hVL hVN
    have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥E // Nat.card M = 3}) ≠ some ⟨N, hN⟩ :=
      fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
    have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
      fun a ha b hb => D.orth _ _ hne a ha b hb
    have horth' : ∀ b ∈ spLineSpace N, ∀ a ∈ spLineSpace L, spForm r K b a = 0 :=
      fun b hb a ha => by rw [← spForm_isAlt.neg_eq, horth a ha b hb, neg_zero]
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := exists_mem_fixing_eq (U := spLineSpace L)
      (D.nondeg (some ⟨L, hL⟩))
      (fun c hc => transCenter_of_mem_summand_three_uni hcard (some ⟨L, hL⟩) hc) hu₀ hy hu₀0 hy0
    obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := exists_mem_fixing_eq (U := spLineSpace N)
      (D.nondeg (some ⟨N, hN⟩))
      (fun c hc => transCenter_of_mem_summand_three_uni hcard (some ⟨N, hN⟩) hc) hw₀ hy' hw₀0 hy'0
    have h2 : spEnd g₂ u₀ = u₀ := hg₂fix u₀ (fun c hc => horth u₀ hu₀ c hc)
    have h1 : spEnd g₁ y' = y' := hg₁fix y' (fun c hc => horth' y' hy' c hc)
    have := hmix.map ((spUniSpan E).mul_mem hg₁ hg₂)
    rwa [spEnd_mul, Module.End.mul_apply, map_add, h2, hg₂w, map_add, hg₁u, h1] at this

theorem uniClosure_spPlane_three [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) : spUniSpan E = ⊤ := by
  classical
  have D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  exact eq_top_of_transCenter (transCenter_of_pairs (Vs := spInnerSummand 3 E)
    D.internal.submodule_iSup_eq_top D.orth D.nondeg
    (fun i c hc => transCenter_of_mem_summand_three_uni hcard i hc)
    (fun i j hij y hy y' hy' hy0 hy'0 =>
      transCenter_pair_three_uni h3 hK hcomm hexp hcard D i j hij hy hy' hy0 hy'0))

end SpPlane

theorem uniClosure_of_lift {G Q : Type*} [Group G] [Group Q] [Finite G] {p n : ℕ}
    [Fact p.Prime] (π : G →* Q) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    (E : Subgroup Q) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hG : ∀ E' : Subgroup G, (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) → (∀ a ∈ E', a ^ p = 1) →
      Nat.card E' = Nat.card E →
      Subgroup.closure {h : G | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h ∧ h ^ n = 1} = ⊤) :
    Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} = ⊤ := by
  classical
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hker E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
  have hfπsurj : Function.Surjective fπ := by
    intro e
    have : (e : Q) ∈ E'.map π := hE'map ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hfπinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  have htop := hG E' hE'comm hE'exp hcard
  rw [eq_top_iff]
  have : (Subgroup.closure {h : G | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h ∧ h ^ n = 1}).map π ≤
      Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨h, ⟨x, hx, hx1, hxc, hhn⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π x, hE'mem x hx, ?_, by rw [← map_mul, ← map_mul, hxc],
      by rw [← map_pow, hhn, map_one]⟩
    intro hπx
    exact hx1 (Subgroup.disjoint_def.mp hE'dis hx (by rwa [MonoidHom.mem_ker]))
  rw [htop, Subgroup.map_top_of_surjective π hπ] at this
  exact this

section SpCat

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)


theorem uniPlaneGen_inner_psp_four_three {d : TauCeti.ValidLieTypeIndex} {ℓ f : ℕ} {K : Type}
    [Field K] (e : Cat d ≃* StatedProj (StatedSp 2 K)) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h4 : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hinner : InnerPlane d 3 E) : UniPlaneGen ℓ E := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card hℓ hK hℓ3
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by omega)
      (Or.inl (Or.inr h4))
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner Nat.prime_three hc hinner)
  have hchar : ringChar K = ℓ := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hℓ hf hK
  rw [← hchar]
  refine uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  refine uniClosure_of_lift (proj 2 K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 2) (K := K))
    ?_ E₁ (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hE₁.2 x hx) ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := 2) (K := K) (by omega) Nat.prime_three (by omega)
    exact Nat.prime_three.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl 3))
  · intro E' hc' he' hcd'
    exact uniClosure_spFour_three h3 (exists_ne_zero_one (by omega)) hc' he'
      (hcd'.trans (hcard₁.trans (by norm_num)))

theorem uniPlaneGen_inner_sp_three {d : TauCeti.ValidLieTypeIndex} {n ℓ f : ℕ} {K : Type}
    [Field K] (e : Cat d ≃* StatedProj (StatedSp n K)) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h4 : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hinner : InnerPlane d 3 E) : UniPlaneGen ℓ E := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card hℓ hK hℓ3
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp n K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n (by omega)
      (Or.inl (Or.inr h4))
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner Nat.prime_three hc hinner)
  have hchar : ringChar K = ℓ := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hℓ hf hK
  rw [← hchar]
  refine uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  refine uniClosure_of_lift (proj n K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := n) (K := K))
    ?_ E₁ (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hE₁.2 x hx) ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := n) (K := K) (by omega) Nat.prime_three (by omega)
    exact Nat.prime_three.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl 3))
  · intro E' hc' he' hcd'
    exact uniClosure_spPlane_three h3 (exists_ne_zero_one (by omega)) hc' he'
      (hcd'.trans (hcard₁.trans (by norm_num)))

theorem uniSeitzPlanes_symplectic_three :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsSymplecticIndex d.1 ∧
      d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, rfl, hsp, hchar2⟩
  rcases hsp with ⟨q, rfl⟩ | ⟨n, q, rfl, -, hq2⟩ | ⟨n, q, rfl⟩
  ·
    have hq : 3 ≠ q.p := by simpa using hpd
    have h4 : 4 ≤ q.p ^ q.exponent := by
      have := (TauCeti.TypeB2LieIndex.of q hv).four_le_fieldOrder
      simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using this
    have hcard := CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv
    have h := uniPlaneGen_inner_psp_four_three
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) q.prime_p (Ne.symm hq)
      q.exponent_pos hcard (by rw [hcard]; exact h4) hE hc hinner
    simpa using h
  ·
    exact absurd (by simpa using hq2) hchar2
  ·
    have hq : 3 ≠ q.p := by simpa using hpd
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hn3 : 3 ≤ n := hrange.1
    have hq2 : q.p ≠ 2 := hrange.2
    have hcard := card_fixedField_C n q hv
    have h4 : 4 ≤ q.p ^ q.exponent := by
      have h5 : 5 ≤ q.p := by
        have := q.prime_p.two_le
        rcases (by omega : q.p = 2 ∨ q.p = 3 ∨ q.p = 4 ∨ 5 ≤ q.p) with h | h | h | h
        · exact absurd h hq2
        · exact absurd h.symm hq
        · exact absurd (h ▸ q.prime_p) (by norm_num)
        · exact h
      calc 4 ≤ q.p := by omega
        _ = q.p ^ 1 := (pow_one _).symm
        _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
    have h := uniPlaneGen_inner_sp_three (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n q hv)
      q.prime_p (Ne.symm hq) q.exponent_pos hcard (by rw [hcard]; exact h4) hn3 hE hc hinner
    simpa using h

end SpCat

section G2Root

open CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem xOp_pow_eq (τ : Tag) {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) (n : ℕ) :
    xOp τ R i c ^ n = xOp τ R i (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, xOp_zero]
  | succ n ih => rw [pow_succ, ih, xOp_mul_xOp (upTransport τ), Nat.cast_succ, add_mul, one_mul]

theorem yOp_pow_eq (τ : Tag) {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) (n : ℕ) :
    yOp τ R i c ^ n = yOp τ R i (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, yOp_zero]
  | succ n ih => rw [pow_succ, ih, yOp_mul_yOp (downTransport τ), Nat.cast_succ, add_mul, one_mul]

theorem closure_pow_ringChar_adjointGroup (τ : Tag) (K : Type) [Field K] :
    Subgroup.closure {g : adjointGroup τ K | g ^ ringChar K = 1} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have key : ∀ (x : ModGL τ K) (hx : x ∈ Subgroup.closure {g : ModGL τ K | ∃ (i : Fin τ.rank) (c : K),
      (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c}),
      (⟨x, hx⟩ : adjointGroup τ K) ∈ Subgroup.closure {g : adjointGroup τ K | g ^ ringChar K = 1} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      show (⟨x, Subgroup.subset_closure hx⟩ : adjointGroup τ K) ^ ringChar K = 1
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      obtain ⟨i, c, h | h⟩ := hx
      · rw [h, xOp_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, xOp_zero]
      · rw [h, yOp_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, yOp_zero]
    | one => exact one_mem _
    | mul x y _ _ ihx ihy => exact mul_mem ihx ihy
    | inv x _ ih => exact inv_mem ih
  exact key g hg

end G2Root

theorem fixedSubgroup_le_closure_of_conj {K : Type*} [Group K] {n : ℕ} {α β c : MulAut K}
    (h : c * α * c⁻¹ = β)
    (hβ : fixedSubgroup β ≤ Subgroup.closure {x | β x = x ∧ x ^ n = 1}) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ n = 1} := by
  have hα : α = c⁻¹ * β * c := by rw [← h]; group
  intro x hx
  have hx' : c x ∈ fixedSubgroup β := by
    have h1 : α x = x := hx
    show β (c x) = c x
    rw [← h]
    simp [MulAut.mul_apply, h1]
  have h1 := Subgroup.mem_map_of_mem c⁻¹.toMonoidHom (hβ hx')
  rw [MonoidHom.map_closure] at h1
  have h2 : c⁻¹.toMonoidHom (c x) = x := by simp
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, ⟨hy, hyn⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hα]
    simp [MulAut.mul_apply, hy]
  · rw [← map_pow, hyn, map_one]

theorem exists_noncomm_of_conj_injective {P : Type*} [Group P] [Nontrivial P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) : ∃ a b : P, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_ne (1 : P)
  apply ha
  apply hinj
  ext y
  rw [MulAut.conj_apply, map_one, MulAut.one_apply, hcon a y, mul_inv_cancel_right]

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.Chevalley CFSG.HardMathSupport.Seitz.G2Noninner
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.Ree


theorem g2Fixed_le_closure {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    g2Fixed σ ≤ Subgroup.closure {x : adjointGroup .G2 K |
      entrywiseAdjointAut .G2 σ x = x ∧ x ^ ringChar K = 1} := by
  have hchar : ringChar (fixSubfield σ) = ringChar K := by
    have : CharP (fixSubfield σ) (ringChar K) := inferInstance
    exact ringChar.eq _ _
  intro y hy
  have hz : g2FixedEquiv σ ⟨y, hy⟩ ∈ Subgroup.closure {z : adjointGroup .G2 (fixSubfield σ) |
      z ^ ringChar (fixSubfield σ) = 1} := by
    rw [closure_pow_ringChar_adjointGroup]
    exact Subgroup.mem_top _
  have h1 : (⟨y, hy⟩ : ↥(g2Fixed σ)) ∈ (Subgroup.closure {z : adjointGroup .G2 (fixSubfield σ) |
      z ^ ringChar (fixSubfield σ) = 1}).map (g2FixedEquiv σ).symm.toMonoidHom := ⟨_, hz, by simp⟩
  rw [MonoidHom.map_closure] at h1
  have h2 := Subgroup.mem_map_of_mem (g2Fixed σ).subtype h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have hmem : (((g2FixedEquiv σ).symm z : ↥(g2Fixed σ)) : adjointGroup .G2 K) ∈
        fixedSubgroup (entrywiseAdjointAut .G2 σ) := by
      rw [fixedSubgroup_entrywise_eq]
      exact ((g2FixedEquiv σ).symm z).2
    exact hmem
  · have hz' : z ^ ringChar K = 1 := by rw [← hchar]; exact hz
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, ← map_pow, hz', map_one, Subgroup.coe_one]

theorem exists_conj_entrywise_G2_ne_three {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (α : MulAut (adjointGroup .G2 K)) (hα : IsOuterOfOrder p α) :
    ∃ (h : adjointGroup .G2 K) (σ : K ≃+* K), orderOf σ = p ∧
      MulAut.conj h * α * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ := by
  classical
  obtain ⟨hNFpt, Θ, hΘspec, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)
  have hNF := conj_normalForm_of_pointwise hNFpt
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hℓ hf hK
  obtain ⟨hord, hout⟩ := hα
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ :=
    odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK hNF hp ⊤
      le_top ⟨α, Subgroup.mem_top _⟩ (fun ⟨g, hg⟩ => hout g hg.symm)
      (by rw [Subgroup.orderOf_mk]; exact hord) x σ hxσ
  set τ : K ≃+* K := Θ δ with hτ
  have hΘτ : Θ (entrywiseAdjointAut .G2 τ) = τ := by
    refine hΘspec _ 1 τ fun h => ?_
    rw [coe_entrywiseAdjointAut]
    simp
  have hker1 : δ⁻¹ * entrywiseAdjointAut .G2 τ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΘτ, ← hτ, inv_mul_cancel]
  rw [hker] at hker1
  obtain ⟨g, hg⟩ := hker1
  have hcomm : τ * σ = σ * τ := by
    let _ := IsCyclic.commGroup (α := K ≃+* K)
    exact mul_comm τ σ
  have hcomm' : entrywiseAdjointAut .G2 σ * entrywiseAdjointAut .G2 τ =
      entrywiseAdjointAut .G2 τ * entrywiseAdjointAut .G2 σ := by
    rw [← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, hcomm]
  refine ⟨g⁻¹, σ, hσp, ?_⟩
  have hgi : MulAut.conj g⁻¹ = (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ := by
    rw [map_inv, hg]
  rw [hgi]
  calc (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ * α * (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹⁻¹
      = (entrywiseAdjointAut .G2 τ)⁻¹ * (δ * α * δ⁻¹) * entrywiseAdjointAut .G2 τ := by
        group
    _ = (entrywiseAdjointAut .G2 τ)⁻¹ * (entrywiseAdjointAut .G2 σ *
          entrywiseAdjointAut .G2 τ) := by rw [hδ, mul_assoc]
    _ = entrywiseAdjointAut .G2 σ := by
        rw [hcomm', inv_mul_cancel_left]

theorem exists_conj_entrywise_G2_three
    {f p : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut (adjointGroup .G2 K))
    (hα : IsOuterOfOrder p α) :
    ∃ (h : adjointGroup .G2 K) (σ : K ≃+* K), orderOf σ = p ∧
      MulAut.conj h * α * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hK
  have : CharP K ReeTag.G2.prime := hchar
  have : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨-, hNF, -, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨hord, hout⟩ := hα
  let α' : MulAut (adjointGroup ReeTag.G2.tag K) := α
  have hord' : orderOf α' = p := hord
  have hout' : ∀ g : adjointGroup ReeTag.G2.tag K, α' ≠ MulAut.conj g := hout
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α'
  obtain ⟨-, -, ⟨σ, -, hσp, hσeq, -⟩, ⟨h, hh⟩, -⟩ :=
    CFSG.RankThree.three_G2_noninner_odd_prime_local_core_trivial hf hK hp hp2 ⊤ le_top
      (⟨α', Subgroup.mem_top _⟩ : (⊤ : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K))))
      (fun ⟨g, hg⟩ => hout' g hg.symm)
      (by rw [Subgroup.orderOf_mk]; exact hord') x a a.2 hxa
  exact ⟨h, σ, hσp, hh.trans hσeq⟩



theorem uniSeitzPlanes_G2_outer :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsG2Index d.1 ∧ d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨q, rfl⟩, hq2⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq2' : q.p ≠ 2 := by simpa using hq2
  have hpq : p ≠ q.p := by simpa using hpd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hchar : ringChar K = q.p := ringChar_eq_of_card_pow q.prime_p q.exponent_pos hK'
  obtain ⟨-, hsimple⟩ := finite_isSimpleGroup_cat_G2 hv
  have : IsSimpleGroup (adjointGroup .G2 K) := MulEquiv.isSimpleGroup e.symm
  have hinj := CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup (τ := .G2) (K := K)
  have hnab : ∃ a b : adjointGroup .G2 K, a * b ≠ b * a := exists_noncomm_of_conj_injective hinj
  have hdata : FieldAutData (adjointGroup .G2 K) p ∧ ∀ τ : MulAut (adjointGroup .G2 K),
      IsOuterOfOrder p τ → ∃ (h : adjointGroup .G2 K) (σ : K ≃+* K), orderOf σ = p ∧
        MulAut.conj h * τ * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ := by
    by_cases h3 : q.p = 3
    · have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK', h3]
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
        · exact absurd h hp2
        · exact absurd (h.trans h3.symm) hpq
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      exact ⟨fieldAutData_G2_three subfieldPairG2Odd q.exponent_pos hK3 hp hp5,
        fun τ hτ => exists_conj_entrywise_G2_three q.exponent_pos hK3 hp hp2 τ hτ⟩
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hpair : SubfieldPairG2AtGe3 K := subfieldPairG2AtGe3 (by rw [hchar]; exact hq2')
      exact ⟨fieldAutData_G2_odd_ne_three_ge3 q.prime_p hq2' h3 q.exponent_pos hK' hp hpair hp3,
        fun τ hτ => exists_conj_entrywise_G2_ne_three q.prime_p hq2' h3 q.exponent_pos hK' hp τ hτ⟩
  obtain ⟨hd, hdesc⟩ := hdata
  have hfix : ∀ τ : MulAut (adjointGroup .G2 K), IsOuterOfOrder p τ →
      fixedSubgroup τ ≤ Subgroup.closure {x | τ x = x ∧ x ^ ringChar K = 1} := by
    intro τ hτ
    obtain ⟨h, σ, -, hh⟩ := hdesc τ hτ
    refine fixedSubgroup_le_closure_of_conj hh ?_
    rw [fixedSubgroup_entrywise_eq]
    exact g2Fixed_le_closure σ
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := uniPlaneGen_of_fieldAutData hnab hp hd hfix (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  rw [hchar] at h
  have h' := (uniPlaneGen_map_congr e _ E).1 h
  simpa using h'

end G2

section E6GroupTheory

open scoped Pointwise

@[expose] def uniCentSet {G : Type*} [Group G] (C A : Subgroup G) (r : ℕ) : Set G :=
  {y | y ∈ C ∧ (∃ a ∈ A, a ≠ 1 ∧ y * a = a * y) ∧ ∃ n : ℕ, y ^ (r ^ n) = 1}

theorem index_dvd_card_of_forall_eq_mulU {P : Type*} [Group P] {Q M : Subgroup P}
    (h : ∀ x : P, ∃ q ∈ Q, ∃ m ∈ M, x = q * m) : M.index ∣ Nat.card Q := by
  classical
  have hq : ∀ x : P ⧸ M, ∃ q ∈ Q, x = q • ((1 : P) : P ⧸ M) := fun x => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, m, hm, rfl⟩ := h a
    refine ⟨q, hq, ?_⟩
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simpa using M.inv_mem hm
  haveI : MulAction.IsPretransitive Q (P ⧸ M) := ⟨fun x y => by
    obtain ⟨q₁, hq₁, rfl⟩ := hq x
    obtain ⟨q₂, hq₂, rfl⟩ := hq y
    refine ⟨⟨q₂ * q₁⁻¹, Q.mul_mem hq₂ (Q.inv_mem hq₁)⟩, ?_⟩
    change (q₂ * q₁⁻¹) • (q₁ • ((1 : P) : P ⧸ M)) = q₂ • ((1 : P) : P ⧸ M)
    rw [smul_smul, inv_mul_cancel_right]⟩
  have h1 := MulAction.index_stabilizer_of_transitive Q ((1 : P) : P ⧸ M)
  rw [Subgroup.index_eq_card, ← h1]
  exact Subgroup.index_dvd_card _

theorem index_subgroupOf_sup_dvd_cardU {G : Type*} [Group G] {Q M : Subgroup G}
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) :
    (M.subgroupOf (Q ⊔ M)).index ∣ Nat.card Q := by
  have hprod : ((Q ⊔ M : Subgroup G) : Set G) = (Q : Set G) * (M : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q M hMQ
  have h := index_dvd_card_of_forall_eq_mulU (P := ↥(Q ⊔ M)) (Q := Q.subgroupOf (Q ⊔ M))
    (M := M.subgroupOf (Q ⊔ M)) (fun x => by
      have hx : (x : G) ∈ (Q : Set G) * (M : Set G) := by
        rw [← hprod]
        exact x.2
      obtain ⟨q, hq, m, hm, hqm⟩ := hx
      refine ⟨⟨q, Subgroup.mem_sup_left hq⟩, hq, ⟨m, Subgroup.mem_sup_right hm⟩, hm,
        Subtype.ext hqm.symm⟩)
  refine h.trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : Q ≤ Q ⊔ M)).toEquiv]



theorem le_closure_uniCentSet_of_map_conj {G : Type*} [Group G] {C A : Subgroup G} {r : ℕ} {x : G}
    (hx : x ∈ Subgroup.normalizer (C : Set G))
    (h : C ≤ Subgroup.closure (uniCentSet C (A.map (MulAut.conj x).toMonoidHom) r)) :
    C ≤ Subgroup.closure (uniCentSet C A r) := by
  have hxC : ∀ y, y ∈ C ↔ x * y * x⁻¹ ∈ C := Subgroup.mem_normalizer_iff.1 hx
  have hxC' : ∀ y, y ∈ C ↔ x⁻¹ * y * x ∈ C := Subgroup.mem_normalizer_iff''.1 hx
  have hle : Subgroup.closure (uniCentSet C (A.map (MulAut.conj x).toMonoidHom) r) ≤
      (Subgroup.closure (uniCentSet C A r)).comap (MulAut.conj x⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyC, ⟨b, hb, hb1, hyb⟩, n, hn⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    have ha1 : a ≠ 1 := fun h => hb1 (by rw [h, map_one])
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine Subgroup.subset_closure ⟨?_, ⟨a, ha, ha1, ?_⟩, n, ?_⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact (hxC' y).1 hyC
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyb
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc x⁻¹ * y * x * a = x⁻¹ * (y * (x * a * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * a * x⁻¹) * y) * x := by rw [hyb]
        _ = a * (x⁻¹ * y * x) := by group
    · rw [← map_pow, hn, map_one]
  intro c hc
  have hmem := hle (h ((hxC c).1 hc))
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
  have e : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
  rwa [e] at hmem

theorem le_closure_uniCentSet_of_coprime {G : Type*} [Group G] {p r : ℕ} [Fact p.Prime]
    {A Q C : Subgroup G} [Finite A] [Finite Q] [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    (hQr : IsPGroup r Q) (hp : ¬ p ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQC : Q ≤ C) : Q ≤ Subgroup.closure (uniCentSet C A r) := by
  have h := CFSG.LieType.Chevalley.le_iSup_inf_centralizer_of_coprime hcard hp hAQ (le_refl Q)
  refine h.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  intro y hy
  obtain ⟨hyQ, hyc⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨n, hn⟩ := hQr ⟨y, hyQ⟩
  refine Subgroup.subset_closure ⟨hQC hyQ, ⟨a, ha, ha1, ?_⟩, n, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.1 hyc a rfl).symm
  · have := congrArg Subtype.val hn
    simpa using this

theorem le_closure_uniCentSet_of_normalizing {G : Type*} [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hrp : r ≠ p)
    {C Q Q' M T A : Subgroup G} [IsSimpleGroup C]
    (hQC : Q ≤ C) (hQ'C : Q' ≤ C) (hMC : M ≤ C) (hTC : T ≤ Subgroup.normalizer (C : Set G))
    (hQp : IsPGroup r Q) (hQ'p : IsPGroup r Q') (hQ1 : Q ≠ ⊥)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hMQ' : M ≤ Subgroup.normalizer (Q' : Set G))
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) (hTQ' : T ≤ Subgroup.normalizer (Q' : Set G))
    (hgen : C ≤ Q ⊔ Q' ⊔ M) [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    {x : G} (hx : x ∈ Subgroup.normalizer (C : Set G))
    (hAx : A.map (MulAut.conj x).toMonoidHom ≤ Q ⊔ (M ⊔ T)) :
    C ≤ Subgroup.closure (uniCentSet C A r) := by
  have hM'Q : M ⊔ T ≤ Subgroup.normalizer (Q : Set G) := sup_le hMQ hTQ
  have hM'Q' : M ⊔ T ≤ Subgroup.normalizer (Q' : Set G) := sup_le hMQ' hTQ'
  have hM'C : M ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hMC.trans Subgroup.le_normalizer) hTC
  have hPC : Q ⊔ (M ⊔ T) ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hQC.trans Subgroup.le_normalizer) hM'C
  have hpQ : ¬ p ∣ Nat.card Q := CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQp
  have hpQ' : ¬ p ∣ Nat.card Q' := CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQ'p
  have hindex : ¬ p ∣ ((M ⊔ T).subgroupOf (Q ⊔ (M ⊔ T))).index := fun h =>
    hpQ (h.trans (index_subgroupOf_sup_dvd_cardU hM'Q))
  have hAxp : IsPGroup p (A.map (MulAut.conj x).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hy, hyA⟩ := CFSG.LieType.Chevalley.exists_conj_le_of_not_dvd_index hAx hAxp hindex
  have hmap : A.map (MulAut.conj (y * x)).toMonoidHom =
      (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hA'' : A.map (MulAut.conj (y * x)).toMonoidHom ≤ M ⊔ T := hmap ▸ hyA
  have : IsElementaryAbelian p (A.map (MulAut.conj (y * x)).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj (y * x)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y * x)).injective]
    exact hcard
  have hyxC : y * x ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.mul_mem _ (hPC hy) hx
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hCX : C ≤ Q ⊔ Q' := by
    have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup G) : Set G) :=
      hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
        CFSG.LieType.Chevalley.mem_normalizer_sup_of_mem (hMQ hm) (hMQ' hm))
    have : ((Q ⊔ Q').subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
    · exfalso
      apply hQ1
      have hdis := Subgroup.subgroupOf_eq_bot.1 h
      exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
        (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
    · exact Subgroup.subgroupOf_eq_top.1 h
  have h1 := le_closure_uniCentSet_of_coprime (r := r) hcard' hQp hpQ (hA''.trans hM'Q) hQC
  have h2 := le_closure_uniCentSet_of_coprime (r := r) hcard' hQ'p hpQ' (hA''.trans hM'Q') hQ'C
  exact le_closure_uniCentSet_of_map_conj hyxC (hCX.trans (sup_le h1 h2))

end E6GroupTheory

section E6Ordinary

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootWeight CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree


variable {τ : Tag} {k : Type} [Field k]

theorem exists_opposite_radicalU [Finite k] {r : ℕ} [Fact r.Prime] [CharP k r]
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    ∃ Q' : Subgroup (ModGL τ k), Q' ≤ adjointGroup τ k ∧ IsPGroup r Q' ∧
      parabolicLevi τ k J ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) ∧
      (rootDiagUnitHom τ k).range ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) ∧
      adjointGroup τ k ≤ parabolicRadical τ k J ⊔ Q' ⊔ parabolicLevi τ k J := by
  have := finite_modGL (τ := τ) (K := k)
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm τ
  obtain ⟨-, hR, -⟩ := canonical_weyl_root_transport τ k
  have hnC : canonicalRep (coxeterSystem τ) k w₀ ∈ adjointGroup τ k :=
    canonicalRep_mem_adjointGroup _ k w₀
  set n := canonicalRep (coxeterSystem τ) k w₀
  set Q := parabolicRadical τ k J
  set Q' := (parabolicRadical τ k (δ '' J)).map (MulAut.conj n⁻¹).toMonoidHom
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin'⟩ :=
    parabolic_root_radical_Levi_factors τ k (δ '' J)
  have hQ'p : IsPGroup r Q' := (hfin' r).2.1.map _
  have hQ'C : Q' ≤ adjointGroup τ k := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnC) (rootSpan_le_adjointGroup k _ hq)) (inv_inv n ▸ hnC)
  have hMQ' : parabolicLevi τ k J ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) := fun m hm =>
    mem_normalizer_map_conj_inv (((parabolicLevi_le_parabolicSubgroup (δ '' J)).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical (δ '' J)))
      (map_conj_parabolicLevi_le hδ J (Subgroup.mem_map_of_mem _ hm)))
  have hTQ' : (rootDiagUnitHom τ k).range ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    refine mem_normalizer_map_conj_inv ?_
    change n * rootDiagUnit τ b * n⁻¹ ∈ _
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_normalizer_parabolicRadical _ _
  have hgen : adjointGroup τ k ≤ Q ⊔ Q' ⊔ parabolicLevi τ k J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ k i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (xUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
        rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
          by rw [height_single]; exact one_pos, i, hi, by simp⟩) c
    · have hg' : g = yUnit τ k i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (yUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
        have hmem : (MulAut.conj n).toMonoidHom (yUnit τ k i c) ∈
            (rootSubgroup τ k (-Pi.single i 1)).map (MulAut.conj n).toMonoidHom :=
          Subgroup.mem_map_of_mem _
            (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_neg_single τ k i c⟩)
        rw [hR w₀ _ (isRoot_neg_single τ i), smul_neg, hδ, neg_neg] at hmem
        have hδi : Pi.single (δ i) 1 ∈ parabolicRadicalRoots τ (δ '' J) :=
          mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ (δ i),
            by rw [height_single]; exact one_pos, δ i,
            fun ⟨j, hj, hji⟩ => hi (hδinj hji ▸ hj), by simp⟩
        have hmem' : (MulAut.conj n).toMonoidHom (yUnit τ k i c) ∈
            parabolicRadical τ k (δ '' J) :=
          (le_biSup (rootSubgroup τ k) hδi) hmem
        refine Subgroup.mem_map.2 ⟨_, hmem', ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MulAut.conj_apply]
        group
  exact ⟨Q', hQ'C, hQ'p, hMQ', hTQ', hgen⟩

theorem ordinary_inndiag_uni (τ : Tag) (k : Type) [Field k]
    [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] (A : Subgroup (ModGL τ k)) (hAC : A ≤ innDiagGL τ k)
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A) (R : Subgroup (ModGL τ k))
    (hRC : R ≤ adjointGroup τ k) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL τ k))) :
    adjointGroup τ k ≤ Subgroup.closure (uniCentSet (adjointGroup τ k) A r) := by
  have := finite_modGL (τ := τ) (K := k)
  set T : Subgroup (ModGL τ k) := (rootDiagUnitHom τ k).range with hT
  have hTC : T ≤ Subgroup.normalizer (adjointGroup τ k : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    exact (root_diagonal_conjugation τ k b).2.2
  have hTD : T ≤ diagonalGroup := by
    rintro _ ⟨b, rfl⟩
    exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_diagonalGroup b
  obtain ⟨g, hg, l, hl, hJ, hAg⟩ := exists_conj_mem_parabolic_sup_of_normalizes
    (RootWeightDatum.ordinary τ : RootWeightDatum k) r (T := T) hTC hTD hRC hRr hR hAC hAR
  set J : Set (Fin τ.rank) := (RootWeightDatum.ordinary τ : RootWeightDatum k).face l
  have hJ' : J ≠ Set.univ := hJ
  obtain ⟨Q', hQ'C, hQ'p, hMQ', hTQ', hgen⟩ := exists_opposite_radicalU (k := k) (r := r) hJ'
  obtain ⟨-, -, -, hMP, -, hPQM, -, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors τ k J
  have hQp : IsPGroup r (parabolicRadical τ k J) := (hfin r).2.1
  have hQ1 : parabolicRadical τ k J ≠ ⊥ := (hfin r).2.2 hJ'
  have hQC : parabolicRadical τ k J ≤ adjointGroup τ k := rootSpan_le_adjointGroup k _
  have hMC : parabolicLevi τ k J ≤ adjointGroup τ k :=
    hMP.trans (parabolicSubgroup_le_adjointGroup τ k J)
  have hMQ : parabolicLevi τ k J ≤ Subgroup.normalizer (parabolicRadical τ k J : Set (ModGL τ k)) :=
    hMP.trans (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hTQ : T ≤ Subgroup.normalizer (parabolicRadical τ k J : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    exact rootDiagUnit_mem_normalizer_parabolicRadical b J
  have hAx : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      parabolicRadical τ k J ⊔ (parabolicLevi τ k J ⊔ T) := by
    rintro _ ⟨a, ha, rfl⟩
    have h : g⁻¹ * a * g ∈ parabolicSubgroup τ k J ⊔ T := hAg a ha
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine (sup_le (hPQM ▸ sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right) : parabolicSubgroup τ k J ⊔ T ≤
        parabolicRadical τ k J ⊔ (parabolicLevi τ k J ⊔ T)) h
  exact le_closure_uniCentSet_of_normalizing hrp hQC hQ'C hMC hTC hQp hQ'p hQ1 hMQ hMQ' hTQ hTQ'
    hgen hcard (Subgroup.le_normalizer (inv_mem hg)) hAx


end E6Ordinary

section E6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.Fischer


theorem e6InndiagUniGeneration (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (hr3 : r ≠ 3) (A : Subgroup (ModGL Tag.E6 K)) (hAC : A ≤ e6InndiagGL K)
    (hAEA : IsElementaryAbelian 3 A) (hcard : 3 ^ 2 ≤ Nat.card A)
    (R : Subgroup (ModGL Tag.E6 K)) (hRC : R ≤ adjointGroup Tag.E6 K) (hRr : IsPGroup r R)
    (hR : R ≠ ⊥) (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL Tag.E6 K))) :
    adjointGroup Tag.E6 K ≤ Subgroup.closure (uniCentSet (adjointGroup Tag.E6 K) A r) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hAEA
  haveI : IsSimpleGroup (adjointGroup Tag.E6 K) :=
    CFSG.SeitzReduction.E6Pilot.isSimpleGroup_adjointGroup_E6
  exact ordinary_inndiag_uni Tag.E6 K r 3 hr3 A hAC hcard R hRC hRr hR hAR

theorem e6InndiagParabolic_uni (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (hEab : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hnin : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) (hnorm : E6NormalizesR K E) :
    UniPlaneGen (ringChar K) E := by
  classical
  have hK4 := four_le_card_of_not_innerAut K hK3 E hE hnin
  have hinj := e6InndiagConj_injective K hK4
  obtain ⟨R, hRC, hR1, hRp, hRn⟩ := matrix_of_e6NormalizesR E hE hnorm
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hAle : e6PlanePre K E ≤ e6InndiagGL K := by
    rintro _ hx
    obtain ⟨g, rfl, -⟩ := (mem_e6PlanePre_iff K E _).1 hx
    exact g.2
  have hAcomm : ∀ a ∈ e6PlanePre K E, ∀ b ∈ e6PlanePre K E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, rfl, hg⟩ := (mem_e6PlanePre_iff K E a).1 ha
    obtain ⟨h, rfl, hh⟩ := (mem_e6PlanePre_iff K E b).1 hb
    have : g * h = h * g := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEab.is_comm.comm ⟨_, hg⟩ ⟨_, hh⟩)
    exact congrArg Subtype.val this
  have hAEA : CFSG.IsElementaryAbelian 3 (e6PlanePre K E) :=
    CFSG.IsElementaryAbelian.of_forall hAcomm fun a ha =>
      pow_three_eq_one_of_mem_e6PlanePre K hK4 E ha
  have hAcard : Nat.card (e6PlanePre K E) = 3 ^ 2 := by
    rw [card_e6PlanePre K hK4 E hE]
    exact hcard
  have hgen := e6InndiagUniGeneration K (ringChar K) hK3 (e6PlanePre K E) hAle hAEA hAcard.ge R hRC
    hRp hR1 hRn
  have hsub : uniCentSet (adjointGroup Tag.E6 K) (e6PlanePre K E) (ringChar K) ⊆
      (uniPlaneClosure (ringChar K) E).map (adjointGroup Tag.E6 K).subtype := by
    rintro y ⟨hyC, ⟨a, ha, ha1, hya⟩, n, hn⟩
    obtain ⟨g, rfl, hgE⟩ := (mem_e6PlanePre_iff K E a).1 ha
    refine ⟨⟨y, hyC⟩, mem_uniPlaneClosure hgE ?_ ?_ (n := n) ?_, rfl⟩
    · intro h1
      have : g = 1 := hinj (by rw [h1, map_one])
      exact ha1 (by rw [this]; rfl)
    · apply Subtype.ext
      rw [e6InndiagConj_apply, mul_inv_eq_iff_eq_mul]
      exact hya.symm
    · apply Subtype.ext
      simpa using hn
  have hle : adjointGroup Tag.E6 K ≤
      (uniPlaneClosure (ringChar K) E).map (adjointGroup Tag.E6 K).subtype :=
    hgen.trans ((Subgroup.closure_le _).2 hsub)
  rw [UniPlaneGen, eq_top_iff]
  intro y _
  obtain ⟨t, ht, hty⟩ := hle y.2
  have : t = y := Subtype.ext hty
  rw [← this]
  exact ht

theorem e6NormalizesR_of_diag (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hEab : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hE : E ≤ e6Inndiag K)
    (hnin : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) : E6NormalizesR K E := by
  have hT : E6InndiagTorality := e6InndiagTorality_of_heisenberg (e6HeisenbergParabolic_of_frame
    (e6HeisFrameNormalizesR_of_fixedElt (e6HeisFrameFixedElt_of_classD e6HeisFrameFixedEltD_holds)))
  rcases hT K hK3 E hE hEab hcard hnin with ⟨D, x, hxA, hxout⟩ | hnorm
  · by_cases hkillex : ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ D.Kills α
    · obtain ⟨α, hα, hkill⟩ := hkillex
      obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ :=
        kill_root_gl_E6 K hK3 (e6PlanePre K E) D α hα hkill
      set U : adjointGroup Tag.E6 K := ⟨u, hu⟩ with hUdef
      have hU1 : U ≠ 1 := by
        intro h
        apply hu1
        have := congrArg Subtype.val h
        simpa [hUdef] using this
      have hUn : U ^ (ringChar K ^ n) = 1 := by
        apply Subtype.ext
        simpa [hUdef] using hn
      have hRp : IsPGroup (ringChar K) (Subgroup.zpowers U) := by
        intro g
        refine ⟨n, Subtype.ext ?_⟩
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hUn, one_zpow]
      refine ⟨Subgroup.zpowers U, ?_, hRp, ?_⟩
      · exact fun h => hU1 (Subgroup.zpowers_eq_bot.1 h)
      · intro ε hεE
        have hεr : ε ∈ (e6InndiagConj K).range := by
          rw [range_e6InndiagConj]
          exact hE hεE
        obtain ⟨g, rfl⟩ := hεr
        have hgA : (g : ModGL Tag.E6 K) ∈ e6PlanePre K E :=
          (mem_e6PlanePre_iff K E _).2 ⟨g, rfl, hεE⟩
        have hfix : e6InndiagConj K g U = U := by
          apply Subtype.ext
          rw [e6InndiagConj_apply]
          show (g : ModGL Tag.E6 K) * u * (g : ModGL Tag.E6 K)⁻¹ = u
          rw [mul_inv_eq_iff_eq_mul]
          exact (hcomm _ hgA).symm
        have hfix' : (e6InndiagConj K g).toMonoidHom U = U := hfix
        rw [MonoidHom.map_zpowers, hfix']
    · exact e6DiagRegularOuter_holds K hK3 E hE hEab hcard D hkillex ⟨x, hxA, hxout⟩
  · exact hnorm

@[expose] def IsE6DiagPlane (d : TauCeti.ValidLieTypeIndex)
    (E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), CharP K q.p ∧
    ∃ e : CFSG.LieType.SeitzGeneration.Cat d ≃* adjointGroup Tag.E6 K,
      E.map (MulAut.congr e).toMonoidHom ≤ e6Inndiag K

theorem uniSeitzPlanes_E6_diag :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsE6DiagPlane d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, rfl, q, rfl, K, _, _, hKq, e, hdiag⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : 3 ≠ q.p := by simpa using hpd
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K q.p]
    exact fun h => hpq h.symm
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hnin : ¬ E.map (MulAut.congr e).toMonoidHom ≤ innerAut (adjointGroup Tag.E6 K) := fun hle =>
    not_le_range_conj_map_congr e hout fun φ hφ => (hle hφ).imp fun g hg => hg
  have hnorm := e6NormalizesR_of_diag K hK3 _ hEi hc' hdiag hnin
  have h := e6InndiagParabolic_uni K hK3 _ hdiag hEi hc' hnin hnorm
  rw [ringChar.eq K q.p] at h
  have h' := (uniPlaneGen_map_congr e _ E).1 h
  simpa using h'

end E6

section FieldExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.SeitzGeneration.ExcWideThree


theorem fixedSubgroup_entrywise_le_closure {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ) :
    fixedSubgroup (entrywiseAdjointAut τ σ) ≤
      Subgroup.closure {x | entrywiseAdjointAut τ σ x = x ∧ x ^ ringChar K = 1} := by
  have hchar : ringChar (fixSubfield σ) = ringChar K := by
    have : CharP (fixSubfield σ) (ringChar K) := inferInstance
    exact ringChar.eq _ _
  set φ := fixedEquivOfEq σ hΓJ with hφ
  intro y hy
  have hz : φ ⟨y, hy⟩ ∈ Subgroup.closure {z : adjointGroup τ (fixSubfield σ) |
      z ^ ringChar (fixSubfield σ) = 1} := by
    rw [closure_pow_ringChar_adjointGroup]
    exact Subgroup.mem_top _
  have h1 : (⟨y, hy⟩ : ↥(fixedSubgroup (entrywiseAdjointAut τ σ))) ∈
      (Subgroup.closure {z : adjointGroup τ (fixSubfield σ) |
        z ^ ringChar (fixSubfield σ) = 1}).map φ.symm.toMonoidHom := ⟨_, hz, by simp⟩
  rw [MonoidHom.map_closure] at h1
  have h2 := Subgroup.mem_map_of_mem (fixedSubgroup (entrywiseAdjointAut τ σ)).subtype h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨(φ.symm z).2, ?_⟩
  have hz' : z ^ ringChar K = 1 := by rw [← hchar]; exact hz
  simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [← SubgroupClass.coe_pow, ← map_pow, hz', map_one, OneMemClass.coe_one]

theorem uniPlaneGen_outer_F4E78 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] [IsSimpleGroup (adjointGroup τ K)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ≠ ringChar K) (E : Subgroup (MulAut (adjointGroup τ K))) [CFSG.IsElementaryAbelian p E]
    (hc : Nat.card E = p ^ 2) (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) :
    UniPlaneGen (ringChar K) E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hinj := CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup (τ := τ) (K := K)
  have hnab := exists_noncomm_of_conj_injective hinj
  have hd : FieldAutData (adjointGroup τ K) p := by
    rcases hτ with rfl | rfl | rfl
    · exact fieldAutData_F4_of_maximalOdd subfieldMaximalAllOdd_F4 hp hp2 hpK
    · exact fieldAutData_E78_of_maximalOdd .E7 (Or.inl rfl)
        (subfieldMaximalAllOdd_of_E .E7 (Or.inr (Or.inl rfl))) hp hp2 hpK
    · exact fieldAutData_E78_of_maximalOdd .E8 (Or.inr rfl)
        (subfieldMaximalAllOdd_of_E .E8 (Or.inr (Or.inr rfl))) hp hp2 hpK
  have hdesc : CFSG.AGLEmbedding.SeitzEqTwo.FieldDescentAt τ K p := by
    rcases hτ with rfl | rfl | rfl
    · exact CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_F4 hℓ n.pos hK hp hp2
    · exact CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (Or.inr (Or.inl rfl)) n.pos hK hp hp2
        (not_dvd_det_cartan_E78 (Or.inl rfl) hp hp2)
    · exact CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (Or.inr (Or.inr rfl)) n.pos hK hp hp2
        (not_dvd_det_cartan_E78 (Or.inr rfl) hp hp2)
  have hΓJ : ∀ σ : K ≃+* K, σ ^ p = 1 → entrywiseFixedGroup τ σ = fixedFieldImage τ σ := by
    intro σ hσ
    rcases hτ with rfl | rfl | rfl
    · exact entrywiseFixedGroup_F4_eq σ
    · exact entrywiseFixedGroup_eq_fixedFieldImage_E7_of_pow σ hσ hcop2
    · exact entrywiseFixedGroup_E8_eq σ
  have hfix : ∀ α : MulAut (adjointGroup τ K), IsOuterOfOrder p α →
      fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ringChar K = 1} := by
    intro α hα
    obtain ⟨hord, hout'⟩ := hα
    have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    have hα' : α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range :=
      fun ⟨g, hg⟩ => hout' g hg.symm
    obtain ⟨T, r, j, ψ, hTo, hj, hψ⟩ := hdesc α hαp hα'
    have hαe : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ (T ^ j) := by
      calc ψ * α * ψ⁻¹ = ψ * (α ^ r) ^ j * ψ⁻¹ := by rw [hj]
        _ = (ψ * α ^ r * ψ⁻¹) ^ j := by rw [conj_pow]
        _ = entrywiseAdjointAut τ T ^ j := by rw [hψ]
        _ = entrywiseAdjointAut τ (T ^ j) := by rw [entrywiseAdjointAut_pow]
    have hTjp : (T ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hTo, pow_orderOf_eq_one, one_pow]
    exact fixedSubgroup_le_closure_of_conj hαe
      (fixedSubgroup_entrywise_le_closure (T ^ j) (hΓJ _ hTjp))
  exact uniPlaneGen_of_fieldAutData hnab hp hd hfix E hc hout

theorem uniPlaneGen_cat_outer_F4E78 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {d : TauCeti.ValidLieTypeIndex} {K : Type} [Field K] [Finite K]
    [IsSimpleGroup (adjointGroup τ K)] (e : Cat d ≃* adjointGroup τ K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ≠ ringChar K) {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane d p E) : UniPlaneGen (ringChar K) E := by
  have : Fact p.Prime := ⟨hp⟩
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  exact (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_outer_F4E78 hτ hp hp2 hpK _ hc' hout')

theorem uniSeitzPlanes_F4E78_outer :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ (IsF4Index d.1 ∨ IsE7Index d.1 ∨ IsE8Index d.1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, hfam⟩
  rcases hfam with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨K, _, _, -, hKchar, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have : IsSimpleGroup (Cat ⟨.F4 q, hv⟩) := (finite_isSimpleGroup_cat_F4 hv).2
    have : IsSimpleGroup (adjointGroup Tag.F4 K) := MulEquiv.isSimpleGroup e.symm
    have h := uniPlaneGen_cat_outer_F4E78 (Or.inl rfl) e hp hp2
      (by rw [hchar]; simpa using hpd) hE hc hout
    rw [hchar] at h
    simpa using h
  · obtain ⟨K, _, _, -, hKchar, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have : IsSimpleGroup (adjointGroup Tag.E7 K) :=
      CFSG.SeitzReduction.E7Pilot.isSimpleGroup_adjointGroup_E7 K
    have h := uniPlaneGen_cat_outer_F4E78 (Or.inr (Or.inl rfl)) e hp hp2
      (by rw [hchar]; simpa using hpd) hE hc hout
    rw [hchar] at h
    simpa using h
  · obtain ⟨K, _, _, -, hKchar, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have : IsSimpleGroup (adjointGroup Tag.E8 K) :=
      CFSG.SeitzReduction.E8Pilot.isSimpleGroup_adjointGroup_E8 K
    have h := uniPlaneGen_cat_outer_F4E78 (Or.inr (Or.inr rfl)) e hp hp2
      (by rw [hchar]; simpa using hpd) hE hc hout
    rw [hchar] at h
    simpa using h

theorem uniPlaneGen_outer_E6_five {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K) (E : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    [CFSG.IsElementaryAbelian p E] (hc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) : UniPlaneGen (ringChar K) E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have : IsSimpleGroup (adjointGroup Tag.E6 K) :=
    CFSG.SeitzReduction.E6Pilot.isSimpleGroup_adjointGroup_E6
  have hinj := CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  have hnab := exists_noncomm_of_conj_injective hinj
  have hd : FieldAutData (adjointGroup Tag.E6 K) p :=
    fieldAutData_E6_of_subfieldMaximalAll subfieldMaximalAll_E6 hp hp5 hpK
  have hdesc : CFSG.AGLEmbedding.SeitzEqTwo.FieldDescentAt Tag.E6 K p :=
    CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (Or.inl rfl) n.pos hK hp hp2
      (not_dvd_det_cartan_E (Or.inl rfl) hp hp3)
  have hfix : ∀ α : MulAut (adjointGroup Tag.E6 K), IsOuterOfOrder p α →
      fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ringChar K = 1} := by
    intro α hα
    obtain ⟨hord, hout'⟩ := hα
    have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    have hα' : α ∉ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range :=
      fun ⟨g, hg⟩ => hout' g hg.symm
    obtain ⟨T, r, j, ψ, hTo, hj, hψ⟩ := hdesc α hαp hα'
    have hαe : ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.E6 (T ^ j) := by
      calc ψ * α * ψ⁻¹ = ψ * (α ^ r) ^ j * ψ⁻¹ := by rw [hj]
        _ = (ψ * α ^ r * ψ⁻¹) ^ j := by rw [conj_pow]
        _ = entrywiseAdjointAut Tag.E6 T ^ j := by rw [hψ]
        _ = entrywiseAdjointAut Tag.E6 (T ^ j) := by rw [entrywiseAdjointAut_pow]
    have hTjp : (T ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hTo, pow_orderOf_eq_one, one_pow]
    exact fixedSubgroup_le_closure_of_conj hαe (fixedSubgroup_entrywise_le_closure (T ^ j)
      (CFSG.HardMathSupport.Lang.E6Descent.entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow
        (T ^ j) hTjp hcop))
  exact uniPlaneGen_of_fieldAutData hnab hp hd hfix E hc hout

theorem uniSeitzPlanes_E6_outer_five :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsE6Index d.1 ∧ 5 ≤ p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨q, rfl⟩, hp5⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, -, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_outer_E6_five hp hp5
    (by rw [hchar]; simpa using hpd) _ hc' hout')
  rw [hchar] at h
  simpa using h

end FieldExc

section SpOuterUni

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
  CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)


theorem fixedSubgroup_fieldAut_le_closure_sp {r : ℕ} [NeZero r] {K : Type} [Field K] {p : ℕ} (hp : Odd p)
    {σ : K ≃+* K} (hσp : σ ^ p = 1) :
    fixedSubgroup (fieldAut r K σ) ≤
      Subgroup.closure {x | fieldAut r K σ x = x ∧ x ^ ringChar K = 1} := by
  have hchar : ringChar (descentField σ) = ringChar K := by
    have : CharP (descentField σ) (ringChar K) := inferInstance
    exact ringChar.eq _ _
  rw [fixedSubgroup_fieldAut_eq_range_sp hp hσp]
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure {g : StatedSp r (descentField σ) |
      ∃ (v : Fin r ⊕ Fin r → descentField σ) (t : descentField σ), g = spTransvection v t} := by
    rw [closure_spTransvection_eq_top]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem (subfieldProj σ) hg
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨_, ⟨v, t, rfl⟩, rfl⟩
  refine ⟨fieldAut_subfieldProj σ _, ?_⟩
  rw [← map_pow, ← hchar, spTransvection_pow_ringChar, map_one]

theorem uniPlaneGen_outer_sp_model {d : TauCeti.ValidLieTypeIndex}
    {r ℓ f p : ℕ} {K : Type} [Field K] (e : Cat d ≃* StatedProj (StatedSp r K))
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) {E : Subgroup (MulAut (Cat d))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane d p E) :
    UniPlaneGen ℓ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : NeZero r := ⟨by omega⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hrq' : ¬ (r = 2 ∧ Nat.card K = 2) := fun h => hrq ⟨h.1, by rw [← hK]; exact h.2⟩
  have : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    isSimpleGroup_statedProj_statedSp_of_two_le hr hrq'
  have hnab : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hnt : Nontrivial (StatedProj (StatedSp r K)) :=
      (CFSG.LieType.Classical.symplectic_projective_nontrivial K r (by omega)).1
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSp r K))
    have hxc : x ∈ Subgroup.center (StatedProj (StatedSp r K)) :=
      Subgroup.mem_center_iff.mpr fun g => h g x
    rw [center_statedProj_statedSp_eq_bot hr, Subgroup.mem_bot] at hxc
    exact hx hxc
  have hd : FieldAutData (StatedProj (StatedSp r K)) p :=
    fieldAutData_projectiveSp_odd (subfieldPairSpOdd subfieldPairSpF2_holds) hr hℓ hf hK hp hp2
  have hchar : ringChar K = ℓ := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hℓ hf hK
  have O : SpOuter ℓ f r K := spOuter hℓ hf hr hK
  have hfix : ∀ α : MulAut (StatedProj (StatedSp r K)), IsOuterOfOrder p α →
      fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ℓ = 1} := by
    intro α hα
    obtain ⟨hord, hout'⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hαE : α ∈ spSemilinearAutGroup r K :=
      mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hord ▸ hpodd)
    have hαD : α ∉ spLinearAutGroup r K := fun hD => by
      have := inner_normal (StatedProj (StatedSp r K))
      obtain ⟨g, hg⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two
        (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hαp
      exact hout' g hg.symm
    obtain ⟨-, σ, hσord, h, -, hαh⟩ := O.descent p hp α hαE hαD hord
    have hσp : σ ^ p = 1 := hσord ▸ pow_orderOf_eq_one σ
    have hconj : h⁻¹ * α * h⁻¹⁻¹ = fieldAut r K σ := by rw [hαh]; group
    rw [← hchar]
    exact fixedSubgroup_le_closure_of_conj hconj (fixedSubgroup_fieldAut_le_closure_sp hpodd hσp)
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout'' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  exact (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_of_fieldAutData hnab hp hd hfix _ hc' hout'')

theorem uniSeitzPlanes_symplectic_outer :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsSymplecticIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hsp⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hsp with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  ·
    have h := uniPlaneGen_outer_sp_model (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp2 le_rfl
      (fun h => hrange.2 ⟨h.1, by simpa [TauCeti.PrimePower.card_def] using h.2⟩) hE hc hout
    simpa using h
  ·
    have h := uniPlaneGen_outer_sp_model
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hp hp2
      (by omega) (fun h => by omega) hE hc hout
    simpa using h
  ·
    have hr3 : 3 ≤ r := hrange.1
    have h := uniPlaneGen_outer_sp_model (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      q.prime_p q.exponent_pos (card_fixedField_C r q hv) hp hp2 (by omega)
      (fun h => by omega) hE hc hout
    simpa using h

end SpOuterUni

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d

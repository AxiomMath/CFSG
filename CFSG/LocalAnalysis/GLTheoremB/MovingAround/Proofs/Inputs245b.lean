module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1211b
import CFSG.LargeExtraspecial.GLRCentCount
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Basic

variable {X : Type} [Group X] [Finite X]

theorem glbCore_two_le_x0 {p : ℕ} (hp : p.Prime) {P B : Subgroup X} (hBP : B ≤ P)
    (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B) : GLBCore p 2 B ≤ Inputs245.x0 p P := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine sSup_le ?_
  rintro _ ⟨D, hDB, hD2, rfl⟩
  have hDe : IsElemAbelian p D := GL83.CompFam.elem_mono hB hDB
  by_cases hD4 : 4 ≤ CFSG.Open.pRank p D
  · exact Inputs245.normalizer_le_x0 (hDB.trans hBP) hD4
  push Not at hD4
  have hDc : Nat.card D = p ^ CFSG.Open.pRank p D := GL83.PiGen.card_eq_pow_pRank hDe
  obtain ⟨m, hm⟩ := hB.isPGroup.exists_card_eq
  have hm4 : 4 ≤ m := by
    rw [hm] at hB4
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hB4
  obtain ⟨E, hEc, hDE, hEB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 4)
    (H := D) (L := B) (by rw [hDc]; exact pow_dvd_pow p hD4.le) (by rw [hm]; exact pow_dvd_pow p hm4)
    hDB
  have hE : IsEkIn p 4 P E := ⟨hEB.trans hBP, GL83.CompFam.elem_mono hB hEB, hEc⟩
  exact Inputs245.normalizer_le_x0' hE hDE hD2

theorem le_pCoreOf_of_le_normalizer {p : ℕ} {Y N : Subgroup X} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set X)) (hNp : IsPGroup p N) : N ≤ pCoreOf p Y := by
  have hn : (N.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
  have hpg : IsPGroup p (N.subgroupOf Y) := hNp.comap_of_injective _ Y.subtype_injective
  have hle : N.subgroupOf Y ≤ CFSG.pCore p ↥Y := le_sSup ⟨hn, hpg⟩
  intro x hx
  exact ⟨⟨x, hNY hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem mem_normalizer_centralizer {K : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (K : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK : ∀ k : X, k ∈ K ↔ g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hg)
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      rw [hK]
      have e : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
      rw [e]
      exact hk
    have h1 := hx _ hk'
    calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * k := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro k hk
    have hk' : g * k * g⁻¹ ∈ K := (hK k).1 hk
    have h1 := hx _ hk'
    calc k * x = g⁻¹ * ((g * k * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h1]
      _ = x * k := by group

theorem inf_centralizer_le_pCoreOf {p : ℕ} {P K : Subgroup X} (hPp : IsPGroup p P)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) :
    P ⊓ Subgroup.centralizer (K : Set X) ≤ pCoreOf p (P ⊔ K) := by
  refine le_pCoreOf_of_le_normalizer (inf_le_left.trans le_sup_left) (sup_le ?_ ?_)
    (hPp.to_le inf_le_left)
  · intro g hg
    exact Inputs245.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer (hPK hg))
  · intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.1 hx.2) k hk
      have e : k * x * k⁻¹ = x := by rw [hxk]; group
      rw [e]
      exact hx
    · intro hx
      have hxk : k * (k * x * k⁻¹) = (k * x * k⁻¹) * k :=
        (Subgroup.mem_centralizer_iff.1 hx.2) k hk
      have e : x = k * x * k⁻¹ :=
        calc x = k⁻¹ * ((k * x * k⁻¹) * k) := by group
          _ = k⁻¹ * (k * (k * x * k⁻¹)) := by rw [hxk]
          _ = k * x * k⁻¹ := by group
      rw [e]
      exact hx

theorem card_le_of_le_cyclic {p : ℕ} (hp : p.Prime) {C E : Subgroup X} [IsCyclic ↥C]
    (hEC : E ≤ C) (hE : IsElemAbelian p E) : Nat.card E ≤ p := by
  by_cases hE1 : E = ⊥
  · rw [hE1, Subgroup.card_bot]
    exact hp.one_lt.le
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  have hwp : (w : X) ^ p = 1 := hE.2 w w.2
  have hw1' : (w : X) ≠ 1 := fun h => hw1 (Subtype.ext h)
  haveI : Fact p.Prime := ⟨hp⟩
  have hwo : orderOf (w : X) = p := orderOf_eq_prime hwp hw1'
  have hZC : Subgroup.zpowers (w : X) ≤ C := (Subgroup.zpowers_le).2 (hEC w.2)
  have hle : E ≤ Subgroup.zpowers (w : X) := fun e he =>
    Inputs245.mem_of_pow_eq_one_of_cyclic hp hZC (by rw [Nat.card_zpowers, hwo]) (hEC he)
      (hE.2 e he)
  calc Nat.card E ≤ Nat.card (Subgroup.zpowers (w : X)) := Subgroup.card_le_of_le hle
    _ = p := by rw [Nat.card_zpowers, hwo]

theorem four_le_pRank_aut {p : ℕ} (hp : p.Prime) {P K : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (h5 : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) (hPK : P ≤ Subgroup.normalizer (K : Set X))
    (hcyc : IsCyclic ↥(pCoreOf p (P ⊔ K))) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hBP, hBel, hBc⟩ := Claims1211b.exists_ekIn' hP h5
  have hstab : GL83.CompFam.stab B K = B := inf_eq_left.2 (hBP.trans hPK)
  have hcen : Nat.card (GL83.CompFam.cen B K) ≤ p := by
    have hle : GL83.CompFam.cen B K ≤ pCoreOf p (P ⊔ K) :=
      (inf_le_inf_right _ hBP).trans (inf_centralizer_le_pCoreOf hP.2.1 hPK)
    haveI := hcyc
    exact card_le_of_le_cyclic hp hle (GL83.CompFam.elem_mono hBel inf_le_left)
  have h := GL83.CompFam.card_stab_le hBel K
  rw [hstab, hBc] at h
  by_contra hlt
  push Not at hlt
  have h1 : p ^ 5 ≤ p ^ 3 * p :=
    h.trans (Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos (by omega)) hcen)
  have h2 : p ^ 3 * p < p ^ 5 := by
    rw [← pow_succ]
    exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end Basic

section Comp

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_center_of_component {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : IsPGroup p (Subgroup.center ↥K) := by
  rintro ⟨z, hz⟩
  obtain ⟨e, n', hn', hnorder⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (isOfFinOrder_of_finite (z : X)).orderOf_pos.ne' p
      hp.one_lt.ne'
  set w : X := (z : X) ^ p ^ e with hw
  have hwn : w ^ n' = 1 := by
    rw [hw, ← pow_mul, ← hnorder, pow_orderOf_eq_one]
  have hwK : w ∈ K := K.pow_mem z.2 _
  have hwc : ∀ k ∈ K, k * w = w * k := by
    intro k hk
    have h1 : (⟨k, hk⟩ : ↥K) * z ^ p ^ e = z ^ p ^ e * ⟨k, hk⟩ :=
      (Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz _)) ⟨k, hk⟩
    have h2 := congrArg Subtype.val h1
    simpa [hw] using h2
  set W : Subgroup X := Subgroup.zpowers w with hWdef
  have hWK : W ≤ K := (Subgroup.zpowers_le).2 hwK
  have hWn : (W.subgroupOf K).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hc : (g : X) * (a : X) = (a : X) * (g : X) := by
      rw [← hi]
      exact (Commute.zpow_right (hwc g g.2) i).eq
    have e1 : ((g * a * g⁻¹ : ↥K) : X) = (a : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc, mul_inv_cancel_right]
    rw [e1]
    exact ha
  have hsn : IsSubnormal W ⊤ := IsSubnormal.step hWK hWn hK.2.1
  have hcop : Nat.Coprime p (Nat.card W) := by
    rw [hWdef, Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hwn)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hn')
  have hWb : W = ⊥ := GL83.CompFam.eq_bot_of_isSubnormal_of_coprime hp hO hsn hcop
  have hw1 : w = 1 := by
    have : w ∈ W := Subgroup.mem_zpowers w
    rw [hWb, Subgroup.mem_bot] at this
    exact this
  refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
  have : (z : X) ^ p ^ e = 1 := hw1
  simpa using this

theorem dvd_card_center_of_component {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hZK : Subgroup.center ↥K ≠ ⊥) :
    p ∣ Nat.card (Subgroup.center ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (isPGroup_center_of_component hp hO hK).exists_card_eq
  rcases k with _ | k
  · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])) hZK
  · rw [hk, pow_succ]
    exact Dvd.intro_left _ rfl

theorem exists_config {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥)
    (hZ : Subgroup.center X ≠ ⊥) {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hZP : IsCyclic ↥(centerOf P)) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hcyc : IsCyclic ↥(pCoreOf p (P ⊔ K))) :
    ∃ (B : Subgroup X) (z : X), B ≤ P ∧ IsElemAbelian p B ∧
      Nat.card B = p ^ CFSG.Open.pRank p (⊤ : Subgroup X) ∧ z ∈ B ∧ z ∈ K ∧
      z ∈ Subgroup.centralizer (K : Set X) ∧ orderOf z = p ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z) ∧
      (∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzZ, hzp⟩ := Inputs245.exists_mem_center_orderOf hp hO hZ
  obtain ⟨B, hBP, hBel, hBc⟩ := Claims1211b.exists_ekIn' hP (le_refl (CFSG.Open.pRank p (⊤ : Subgroup X)))
  have hzc : ∀ g : X, g * z = z * g := fun g => (Subgroup.mem_center_iff.1 hzZ) g
  have hzpow : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
  have hzB : z ∈ B := by
    by_contra hzB
    have hc := Inputs245.card_sup_zpowers hp hzpow hzB (fun a _ => hzc a)
    have hel := Inputs245.isElemAbelian_sup_zpowers hBel hzpow (fun a _ => hzc a)
    have hle := CFSG.SectionRank.le_pRank hp.one_lt (le_top : B ⊔ Subgroup.zpowers z ≤ ⊤) hel
      (k := CFSG.Open.pRank p (⊤ : Subgroup X) + 1) (by rw [hc, hBc, pow_succ])
    omega
  obtain ⟨t, htPK, ht, -⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp hp2 hO (Inputs245.sylowOf hP) hK
  have hPK' : P ⊓ K ≠ ⊥ := by
    intro h
    have : t ∈ P ⊓ K := htPK
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hzK : z ∈ K := Inputs245.mem_of_le_normalizer hp hP hZP hzZ hzp hPK hPK'
  have hzC : z ∈ Subgroup.centralizer (K : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun g _ => hzc g
  set C : Subgroup X := pCoreOf p (P ⊔ K) with hCdef
  haveI := hcyc
  have hPC : P ⊓ Subgroup.centralizer (K : Set X) ≤ C := inf_centralizer_le_pCoreOf hP.2.1 hPK
  have hzCC : z ∈ C := hPC ⟨hBP hzB, hzC⟩
  have hZC : Subgroup.zpowers z ≤ C := (Subgroup.zpowers_le).2 hzCC
  have hZc : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzp]
  have hKC : K ⊓ Subgroup.centralizer (K : Set X) ≤ C := by
    refine le_pCoreOf_of_le_normalizer (inf_le_left.trans le_sup_right) (sup_le ?_ ?_) ?_
    · intro g hg
      exact Inputs245.mem_normalizer_inf (hPK hg) (mem_normalizer_centralizer (hPK hg))
    · intro g hg
      exact Inputs245.mem_normalizer_inf (Subgroup.le_normalizer hg)
        (mem_normalizer_centralizer (Subgroup.le_normalizer hg))
    · have hZp := isPGroup_center_of_component hp hO hK
      intro x
      obtain ⟨k, hk⟩ := hZp ⟨⟨x, x.2.1⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.1 x.2.2) g g.2)⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun y : Subgroup.center ↥K => ((y : ↥K) : X)) hk
      simpa using this
  refine ⟨B, z, hBP, hBel, hBc, hzB, hzK, hzC, hzp, ?_, ?_⟩
  · intro b hb hbC
    exact Inputs245.mem_of_pow_eq_one_of_cyclic hp hZC hZc (hPC ⟨hBP hb, hbC⟩) (hBel.2 b hb)
  · intro c hc hcC hcp
    exact Inputs245.mem_of_pow_eq_one_of_cyclic hp hZC hZc (hKC ⟨hc, hcC⟩) hcp

theorem closure_gens_eq_top {B K : Subgroup X} {z : X} (hzC : z ∈ Subgroup.centralizer (K : Set X))
    {E : Subgroup (MulAut ↥K)}
    (hEB : ∀ ε ∈ E, ∃ f ∈ B, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹)
    (hcl : Subgroup.closure
      {k : ↥K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center ↥K} = ⊤) :
    Subgroup.closure {k : ↥K | ∃ f ∈ B, f ∉ Subgroup.zpowers z ∧
      f * (k : X) * f⁻¹ * (k : X)⁻¹ ∈ Subgroup.centralizer (K : Set X)} = ⊤ := by
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono ?_
  rintro k ⟨ε, hε, hε1, hk⟩
  obtain ⟨f, hfB, hf⟩ := hEB ε hε
  refine ⟨f, hfB, ?_, ?_⟩
  · intro hfz
    apply hε1
    have hfc : f ∈ Subgroup.centralizer (K : Set X) := (Subgroup.zpowers_le.mpr hzC) hfz
    ext y
    rw [hf y, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hfc (y : X) y.2
    rw [← this, mul_inv_cancel_right]
  · have hc := Subgroup.mem_center_iff.mp hk
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h1 := congrArg (fun a : ↥K => (a : X)) (hc ⟨y, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf] at h1
    exact h1

theorem le_x0_of_lie (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥) (hZ : Subgroup.center X ≠ ⊥)
    (h5 : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hZP : IsCyclic ↥(centerOf P)) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hcyc : IsCyclic ↥(pCoreOf p (P ⊔ K)))
    {d : TauCeti.ValidLieTypeIndex} (hchar : p ≠ d.1.characteristic)
    (hnex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) : K ≤ Inputs245.x0 p P := by
  obtain ⟨B, z, hBP, hBel, hBc, hzB, hzK, hzC, hzp, hCB, hΩ⟩ :=
    exists_config hp hp2 hO hZ hP hZP hK hPK hcyc
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := hBP.trans hPK
  have hB4 : p ^ 4 ≤ Nat.card B := by
    rw [hBc]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hB3 : p ^ 3 ≤ Nat.card B := (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hB4
  obtain ⟨E, hEel, hEcard, hEB⟩ := GL83.I243.exists_plane_image hp hBN hBel hzB hzp hCB hB3
  have hperf : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have hcl := GL83.I243.closure_fix_lift hperf e (fun _ => True)
    (fun E' hE' hc _ => hS d p hp hp2 hchar hnex E' hE' hc) E hEel hEcard trivial
  have hgen := closure_gens_eq_top hzC hEB hcl
  have hle := GL83.I243.le_core_of_closure hp hp2 hK.2.2.1 hBel hBN hzB hzK hzC hzp hΩ hgen
  exact hle.trans (glbCore_two_le_x0 hp hBP hBel hB4)

theorem ker_conj_eq_center (K : Type*) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx := congrArg (fun φ : MulAut K => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = (g * x * g⁻¹) * g := by rw [hx]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x).symm

theorem pRank_aut_le_two_of_out {K : Type} [Group K] [Finite K]
    (hOut : CFSG.AGLEmbedding.KOutTwoGroup K) (h27 : ¬ 3 ^ 3 ∣ Nat.card (K ⧸ Subgroup.center K)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun β : MulAut K => (β : K → K)) fun _ _ h => MulEquiv.ext (congrFun h)
  set I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hI
  have hIcard : Nat.card I = Nat.card (K ⧸ Subgroup.center K) := by
    rw [← ker_conj_eq_center K]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).toEquiv).symm
  refine CFSG.SectionRank.pRank_le (by norm_num) fun A _ hA => ?_
  have hAI : A ≤ I := by
    intro a ha
    obtain ⟨k₁, hk₁⟩ := hOut a
    have hcop : Nat.Coprime (2 ^ k₁) 3 := Nat.Coprime.pow_left k₁ (by norm_num)
    exact GL83.I243.mem_of_pow_mem_of_pow_eq_one hcop hk₁ (hA.2 a ha)
  obtain ⟨j, hj⟩ := hA.isPGroup.exists_card_eq
  have hdvd : 3 ^ j ∣ Nat.card (K ⧸ Subgroup.center K) := by
    rw [← hj, ← hIcard]
    exact Subgroup.card_dvd_of_le hAI
  rw [hj]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hj2
  exact h27 ((pow_dvd_pow 3 (by omega)).trans hdvd)

theorem pRank_aut_le_two_of_small (hSmall : GL83.I243.SmallThreeFacts) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) {i : TauCeti.CFSGIndex}
    (hi : GL83.I243.IsThreeSmallIndex i) (he : Nonempty (K ⧸ Subgroup.center K ≃* i.Group)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨hOut, -, h27⟩ := hSmall K hq i hi he
  exact pRank_aut_le_two_of_out hOut h27

theorem pRank_aut_le_two_of_lfour (hL4 : GL83.I243.LFourFacts) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun β : MulAut K => (β : K → K)) fun _ _ h => MulEquiv.ext (congrFun h)
  haveI : Finite (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    Finite.of_injective (fun β : MulAut (TauCeti.CFSGIndex.lie d).Group => (β : _ → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨-, hrk, -⟩ := hL4 d hd
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  have hρ : Function.Injective ((MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)) :=
    (MulAut.congr e).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _)
  exact (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) _ hρ).trans hrk

end Comp

theorem pRank_aut_le_three_of_j3 (hJ3 : CFSG.AGLEmbedding.KFactJ3OuterRank) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 3 := by
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨hOut, hrk⟩ := hJ3 (K ⧸ Subgroup.center K) ⟨e⟩
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_of_nonabelian hq.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq)
  have hOut3 : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (K ⧸ Subgroup.center K)) := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
  exact h1.trans ((CFSG.AGLEmbedding.pRank_top_mulAut_le_of_not_dvd Nat.prime_three hZ hOut3).trans
    hrk.le)

theorem mem_inner_of_pow_mem {K : Type} [Group K] {α : MulAut K} {i k : ℕ}
    (h3 : α ^ 3 ^ i ∈ (MulAut.conj : K →* MulAut K).range)
    (h2 : α ^ 2 ^ k ∈ (MulAut.conj : K →* MulAut K).range) :
    α ∈ (MulAut.conj : K →* MulAut K).range := by
  have hcop : Nat.Coprime (3 ^ i) (2 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have e : α = (α ^ 3 ^ i) ^ u * (α ^ 2 ^ k) ^ v := by
    rw [← zpow_natCast α (3 ^ i), ← zpow_natCast α (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add,
      mul_comm _ u, mul_comm _ v, huv, zpow_one]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ h3 u) (Subgroup.zpow_mem _ h2 v)

section ONan

open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem exists_pow_mul_eq {K : Subgroup X} {g k : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    (hk : k ∈ K) (n : ℕ) : ∃ k' ∈ K, (g * k) ^ n = g ^ n * k' := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by rw [pow_zero, pow_zero, one_mul]⟩
  | succ n ih =>
    obtain ⟨k', hk', h⟩ := ih
    have hk'' : g⁻¹ * k' * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) k').1 hk'
      rwa [inv_inv] at this
    refine ⟨g⁻¹ * k' * g * k, K.mul_mem hk'' hk, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem isPGroup_sup_inf_centralizer {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    {P K : Subgroup X} (hPp : IsPGroup p P) (hPK : P ≤ Subgroup.normalizer (K : Set X))
    (hK : IsComponentOf K ⊤) : IsPGroup p ↥((P ⊔ K) ⊓ Subgroup.centralizer (K : Set X)) := by
  rintro ⟨x, hxPK, hxC⟩
  have hx : x ∈ (P : Set X) * (K : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P K hPK]
    exact hxPK
  obtain ⟨g, hg, k, hk, rfl⟩ := hx
  obtain ⟨a, ha⟩ := hPp ⟨g, hg⟩
  have hga : g ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨k', hk', hpow⟩ := exists_pow_mul_eq (hPK hg) hk (p ^ a)
  rw [hga, one_mul] at hpow
  have hk'C : k' ∈ Subgroup.centralizer (K : Set X) := hpow ▸ Subgroup.pow_mem _ hxC _
  obtain ⟨b, hb⟩ := isPGroup_center_of_component hp hO hK ⟨⟨k', hk'⟩, Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.1 hk'C) y y.2)⟩
  have hk'b : k' ^ p ^ b = 1 := by
    have := congrArg (fun y : Subgroup.center ↥K => ((y : ↥K) : X)) hb
    simpa using this
  refine ⟨a + b, Subtype.ext ?_⟩
  show (g * k) ^ p ^ (a + b) = 1
  rw [pow_add, pow_mul, hpow, hk'b]

@[expose] def liftIn (K E : Subgroup X) : Subgroup X where
  carrier := {k | k ∈ K ∧ ∃ x ∈ E, k⁻¹ * x ∈ Subgroup.centralizer (K : Set X)}
  one_mem' := ⟨K.one_mem, 1, E.one_mem, by rw [inv_one, one_mul]; exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨haK, x, hx, hax⟩ ⟨hbK, y, hy, hby⟩
    refine ⟨K.mul_mem haK hbK, x * y, E.mul_mem hx hy, ?_⟩
    have hc : b⁻¹ * (a⁻¹ * x) = (a⁻¹ * x) * b⁻¹ :=
      (Subgroup.mem_centralizer_iff.1 hax) b⁻¹ (K.inv_mem hbK)
    have e1 : (a * b)⁻¹ * (x * y) = (a⁻¹ * x) * (b⁻¹ * y) := by
      calc (a * b)⁻¹ * (x * y) = (b⁻¹ * (a⁻¹ * x)) * y := by group
        _ = ((a⁻¹ * x) * b⁻¹) * y := by rw [hc]
        _ = (a⁻¹ * x) * (b⁻¹ * y) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hax hby
  inv_mem' := by
    rintro a ⟨haK, x, hx, hax⟩
    refine ⟨K.inv_mem haK, x⁻¹, E.inv_mem hx, ?_⟩
    have hc : a * (a⁻¹ * x)⁻¹ = (a⁻¹ * x)⁻¹ * a :=
      (Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hax)) a haK
    have e1 : a⁻¹⁻¹ * x⁻¹ = (a⁻¹ * x)⁻¹ := by
      calc a⁻¹⁻¹ * x⁻¹ = a * (a⁻¹ * x)⁻¹ * a⁻¹ := by group
        _ = (a⁻¹ * x)⁻¹ * a * a⁻¹ := by rw [hc]
        _ = (a⁻¹ * x)⁻¹ := by group
    rw [e1]
    exact Subgroup.inv_mem _ hax

theorem mem_liftIn {K E : Subgroup X} {k : X} :
    k ∈ liftIn K E ↔ k ∈ K ∧ ∃ x ∈ E, k⁻¹ * x ∈ Subgroup.centralizer (K : Set X) :=
  Iff.rfl

theorem liftIn_comm {K E : Subgroup X} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hC : ∀ k ∈ K, ∀ l ∈ K, ∀ x ∈ E, ∀ y ∈ E, k⁻¹ * x ∈ Subgroup.centralizer (K : Set X) →
      l⁻¹ * y ∈ Subgroup.centralizer (K : Set X) → (k⁻¹ * x) * (l⁻¹ * y) = (l⁻¹ * y) * (k⁻¹ * x))
    {k l : X} (hk : k ∈ liftIn K E) (hl : l ∈ liftIn K E) : k * l = l * k := by
  obtain ⟨hkK, x, hx, hkx⟩ := hk
  obtain ⟨hlK, y, hy, hly⟩ := hl
  have hcd := hC k hkK l hlK x hx y hy hkx hly
  have hcl : l * (k⁻¹ * x) = (k⁻¹ * x) * l := (Subgroup.mem_centralizer_iff.1 hkx) l hlK
  have hdk : k * (l⁻¹ * y) = (l⁻¹ * y) * k := (Subgroup.mem_centralizer_iff.1 hly) k hkK
  have h1 : x * y = k * l * ((k⁻¹ * x) * (l⁻¹ * y)) := by
    calc x * y = k * (k⁻¹ * x) * (l * (l⁻¹ * y)) := by group
      _ = k * (l * (k⁻¹ * x)) * (l⁻¹ * y) := by rw [hcl]; group
      _ = k * l * ((k⁻¹ * x) * (l⁻¹ * y)) := by group
  have h2 : y * x = l * k * ((k⁻¹ * x) * (l⁻¹ * y)) := by
    calc y * x = l * (l⁻¹ * y) * (k * (k⁻¹ * x)) := by group
      _ = l * (k * (l⁻¹ * y)) * (k⁻¹ * x) := by rw [hdk]; group
      _ = l * k * ((l⁻¹ * y) * (k⁻¹ * x)) := by group
      _ = l * k * ((k⁻¹ * x) * (l⁻¹ * y)) := by rw [hcd]
  exact mul_right_cancel (h1.symm.trans ((hE x hx y hy).trans h2))

theorem false_of_onan (hSpo : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hON : Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group = 460815505920)
    (hO : GLAPPrimeCore 3 X = ⊥) (h5 : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {P : Subgroup X}
    (hP : IsSylowIn 3 ⊤ P) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hZK : Subgroup.center ↥K ≠ ⊥)
    (hcyc : IsCyclic ↥(pCoreOf 3 (P ⊔ K)))
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hOut : CFSG.AGLEmbedding.KOutTwoGroup ↥K := by
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
    have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hq
    exact CFSG.AGLEmbedding.kOutTwoGroup_of_card_outer_le_two hq
      (hSpo (↥K ⧸ Subgroup.center ↥K) inferInstance hnab .ONan ⟨e⟩)
  obtain ⟨E, hEP, hEel, hEc⟩ := Claims1211b.exists_ekIn' hP h5
  have hEN : E ≤ Subgroup.normalizer (K : Set X) := hEP.trans hPK
  set O : Subgroup X := pCoreOf 3 (P ⊔ K)
  haveI := hcyc
  have hC₁O : (P ⊔ K) ⊓ Subgroup.centralizer (K : Set X) ≤ O := by
    refine le_pCoreOf_of_le_normalizer inf_le_left (sup_le ?_ ?_)
      (isPGroup_sup_inf_centralizer Nat.prime_three hO hP.2.1 hPK hK)
    · intro g hg
      exact Inputs245.mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_left hg))
        (mem_normalizer_centralizer (hPK hg))
    · intro g hg
      exact Inputs245.mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_right hg))
        (mem_normalizer_centralizer (Subgroup.le_normalizer hg))
  have hOP : O ≤ P := Inputs245.pCoreOf_le_of_isSylowIn hP le_sup_left
  have hOc : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := ↥O)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmemO : ∀ k ∈ K, ∀ x ∈ E, k⁻¹ * x ∈ Subgroup.centralizer (K : Set X) → k⁻¹ * x ∈ O :=
    fun k hk x hx hkx => hC₁O ⟨(P ⊔ K).mul_mem (Subgroup.mem_sup_right (K.inv_mem hk))
      (Subgroup.mem_sup_left (hEP hx)), hkx⟩
  have hinner : ∀ x ∈ E, ∃ k ∈ K, k⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    intro x hx
    set α : MulAut ↥K := K.normalizerMonoidHom ⟨x, hEN hx⟩ with hα
    have hα3 : α ^ 3 ^ 1 ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
      have hx3 : (⟨x, hEN hx⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hEel.2 x hx)
      rw [pow_one, hα, ← map_pow, hx3, map_one]
      exact Subgroup.one_mem _
    obtain ⟨n, hn⟩ := hOut α
    obtain ⟨k, hk⟩ := mem_inner_of_pow_mem hα3 hn
    refine ⟨k, k.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have h1 : (k : X) * y * (k : X)⁻¹ = x * y * x⁻¹ := by
      have h := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) hk
      have h2 : ((α ⟨y, hy⟩ : ↥K) : X) = x * y * x⁻¹ := rfl
      rw [← h2, ← h, MulAut.conj_apply]
      rfl
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (k : X)⁻¹ * x * y := by group
  set A : Subgroup X := liftIn K E
  have hAK : A ≤ K := fun a ha => ha.1
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    liftIn_comm (fun x hx y hy => GL83.CompFam.elem_comm hEel hx hy)
      (fun k hk l hl x hx y hy hkx hly => hOc _ (hmemO k hk x hx hkx) _ (hmemO l hl y hy hly)) ha hb
  have hAP : A ≤ P := by
    rintro a ⟨haK, x, hx, hax⟩
    have e1 : a = x * (a⁻¹ * x)⁻¹ := by group
    rw [e1]
    exact P.mul_mem (hEP hx) (P.inv_mem (hOP (hmemO a haK x hx hax)))
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAK.trans Subgroup.le_normalizer
  let ψA : ↥A →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  let ψE : ↥E →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hrange : ψE.range ≤ ψA.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hkK, hkx⟩ := hinner x x.2
    refine ⟨⟨k, hkK, x, x.2, hkx⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
    show k * (y : X) * k⁻¹ = (x : X) * y * (x : X)⁻¹
    have h := (Subgroup.mem_centralizer_iff.1 hkx) y y.2
    calc k * (y : X) * k⁻¹ = k * ((y : X) * (k⁻¹ * x)) * (x : X)⁻¹ := by group
      _ = k * ((k⁻¹ * x) * y) * (x : X)⁻¹ := by rw [h]
      _ = (x : X) * y * (x : X)⁻¹ := by group
  have hkerE : Nat.card ψE.ker ≤ 3 := by
    have hle : ψE.ker.map E.subtype ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      refine hC₁O ⟨Subgroup.mem_sup_left (hEP x.2), Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have h1 : ψE x = 1 := hx
      have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) h1
      have h3 : (x : X) * y * (x : X)⁻¹ = y := h2
      calc y * (x : X) = (x : X) * y * (x : X)⁻¹ * (x : X) := by rw [h3]
        _ = (x : X) * y := by group
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    exact card_le_of_le_cyclic Nat.prime_three hle
      (GL83.CompFam.elem_mono hEel (Subgroup.map_subtype_le _))
  have hrangeE : 81 ≤ Nat.card ψE.range := by
    have h := Subgroup.card_ker_mul_card_range ψE
    rw [hEc] at h
    nlinarith
  have hkerA : Nat.card (Subgroup.center ↥K) ≤ Nat.card ψA.ker := by
    have hle : centerOf K ≤ ψA.ker.map A.subtype := by
      intro z hz
      obtain ⟨hzK, hzc⟩ := (Lemma1211.mem_centerOf_iff' K z).1 hz
      have hzC : z ∈ Subgroup.centralizer (K : Set X) :=
        Subgroup.mem_centralizer_iff.2 fun k hk => hzc k hk
      have hzA : z ∈ A := ⟨hzK, 1, E.one_mem, by rw [mul_one]; exact Subgroup.inv_mem _ hzC⟩
      refine ⟨⟨z, hzA⟩, MonoidHom.mem_ker.2 (MulEquiv.ext fun y => Subtype.ext ?_), rfl⟩
      show z * (y : X) * z⁻¹ = y
      rw [← hzc y y.2, mul_inv_cancel_right]
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective A.subtype_injective] at h1
    rwa [centerOf, Subgroup.card_map_of_injective K.subtype_injective] at h1
  have hAcard : 81 * Nat.card (Subgroup.center ↥K) ≤ Nat.card A := by
    rw [← Subgroup.card_ker_mul_card_range ψA, mul_comm 81]
    exact Nat.mul_le_mul hkerA (hrangeE.trans (Subgroup.card_le_of_le hrange))
  set A' : Subgroup ↥K := A.subgroupOf K
  have hA'p : IsPGroup 3 ↥A' := (hP.2.1.to_le hAP).comap_of_injective _ K.subtype_injective
  have hA'c : Nat.card ↥A' = Nat.card ↥A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hKc : Nat.card ↥K = 460815505920 * Nat.card (Subgroup.center ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K), Nat.card_congr e.toEquiv, hON]
  have hidx : ¬ 3 ∣ A'.index := by
    rintro ⟨t, ht⟩
    have h := Subgroup.card_mul_index A'
    obtain ⟨z, hz⟩ := (isPGroup_center_of_component Nat.prime_three hO hK).exists_card_eq
    obtain ⟨a, ha⟩ := hA'p.exists_card_eq
    have hge : 3 ^ (4 + z) ≤ 3 ^ a := by
      rw [pow_add, ← hz, ← ha, hA'c]
      exact hAcard
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.pow_le_pow_iff_right (by norm_num)).1 hge)
    rw [ha, ht, hKc, hz] at h
    have e1 : 3 ^ (4 + z + d) * (3 * t) = 3 ^ z * (243 * (3 ^ d * t)) := by ring
    rw [e1, mul_comm 460815505920] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 3) z) h
    generalize 3 ^ d * t = u at h2
    omega
  have hcomm : IsMulCommutative ↥A' :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.1 a.2) _
      (Subgroup.mem_subgroupOf.1 b.2)))⟩⟩
  have hns := GL83.not_isMulCommutative_sylow_of_perfect hq.1
    (dvd_card_center_of_component Nat.prime_three hO hK hZK) (hA'p.toSylow hidx)
  rw [IsPGroup.toSylow_coe] at hns
  exact hns hcomm

end ONan

@[expose] def Input24_5_compCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore 3 X = ⊥ → Subgroup.center X ≠ ⊥ → 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ P : Subgroup X, IsSylowIn 3 ⊤ P → IsCyclic ↥(centerOf P) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → P ≤ Subgroup.normalizer (K : Set X) →
      Subgroup.center ↥K ≠ ⊥ → IsCyclic ↥(pCoreOf 3 (P ⊔ K)) →
      (∃ i : TauCeti.CFSGIndex, GL83.I243.IsThreeCoverIndex i ∧ i ≠ .sporadic .J3 ∧ i ≠ .sporadic .ONan ∧
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* i.Group)) →
      K ≤ Inputs245.x0 3 P

theorem input24_5_comp_of_cover (hList : GL83.I243.PCoverList)
    (hSmall : GL83.I243.SmallThreeFacts) (hL4 : GL83.I243.LFourFacts)
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hJ3 : CFSG.AGLEmbedding.KFactJ3OuterRank)
    (hSpo : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hON : Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group = 460815505920)
    (hres : Input24_5_compCover) : Inputs245.Input24_5_comp := by
  intro X _ _ p hKX hp hp2 hO hZ h5 P hP hZP K hK hPK hZK hcyc
  have hpZ := dvd_card_center_of_component hp hO hK hZK
  obtain ⟨i, ⟨e⟩⟩ := (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.2 hKX).isCatalogGroup_center_quotient hK
  have h4 := four_le_pRank_aut hp hP h5 hPK hcyc
  rcases hList ↥K hK.2.2 p hp hp2 hpZ i ⟨e⟩ with ⟨d, rfl, hchar, hnex, -⟩ |
    ⟨rfl, hcov | ⟨hsm | hl4, -⟩⟩
  · exact le_x0_of_lie hS hp hp2 hO hZ h5 hP hZP hK hPK hcyc hchar hnex e
  · by_cases hJ : i = .sporadic .J3
    · subst hJ
      exact absurd (pRank_aut_le_three_of_j3 hJ3 hK.2.2 e) (by omega)
    by_cases hN : i = .sporadic .ONan
    · subst hN
      exact (false_of_onan hSpo hON hO h5 hP hK hPK hZK hcyc e).elim
    exact hres X hKX hO hZ h5 P hP hZP K hK hPK hZK hcyc ⟨i, hcov, hJ, hN, ⟨e⟩⟩
  · exact absurd (pRank_aut_le_two_of_small hSmall hK.2.2 hsm ⟨e⟩) (by omega)
  · obtain ⟨d, rfl, hd⟩ := hl4
    exact absurd (pRank_aut_le_two_of_lfour hL4 hK.2.2 hd e) (by omega)

section Small

variable {X : Type} [Group X] [Finite X]

theorem exists_component_of_not_isPConstrained {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p X = ⊥) (h : ¬ CFSG.ABGLocalTools.IsPConstrained p X) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hno
  push Not at hno
  apply h
  have hlayer : CFSG.layer X = ⊥ := by
    rw [CFSG.layer_eq_componentClassification,
      CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    exact sSup_eq_bot.2 fun K hK => absurd hK (hno K)
  have hchar : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p hO hlayer
  have hOp : CFSG.pCore p X ≤ CFSG.Op_p'p p X := by
    refine CFSG.ABGLocalTools.le_Op_p'p_of_normal CFSG.pCore_normal fun x hx => ?_
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)) ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact Subgroup.one_mem _
  intro S hS
  obtain ⟨Q, rfl⟩ := hS
  have hn : ((CFSG.pCore p X).subgroupOf (CFSG.Op_p'p p X)).Normal :=
    Subgroup.Normal.subgroupOf CFSG.pCore_normal _
  have hpg : IsPGroup p ((CFSG.pCore p X).subgroupOf (CFSG.Op_p'p p X)) :=
    (CFSG.pCore_isPGroup (p := p) (G := X)).comap_of_injective _ (Subgroup.subtype_injective _)
  have hle : (CFSG.pCore p X).subgroupOf (CFSG.Op_p'p p X) ≤ Q := hpg.le_sylow_of_normal Q
  have hPS : CFSG.pCore p X ≤ (Q : Subgroup ↥(CFSG.Op_p'p p X)).map (CFSG.Op_p'p p X).subtype := by
    intro x hx
    exact ⟨⟨x, hOp hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  exact (Subgroup.centralizer_le hPS).trans (hchar.trans hOp)

end Small

@[expose] def Input24_5_smallThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore 3 X = ⊥ → Subgroup.center X ≠ ⊥ → 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ P : Subgroup X, IsSylowIn 3 ⊤ P → IsCyclic ↥(centerOf P) →
      ¬ CFSG.ABGLocalTools.IsPConstrained 3 X →
      (∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥) →
      CFSG.ComponentClassification.Layer.subgroup X ≤ Inputs245.x0 3 P →
      CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3 →
        Inputs245.x0 3 P = ⊤

theorem input24_5_small_of_three
    (hRank : CFSG.LocalAnalysis.RankThreeTheoremC.SchurMultiplierRankFact)
    (hres : Input24_5_smallThree) : Inputs245.Input24_5_small := by
  intro X _ _ p hKX hp hp2 hO hZ h5 P hP hZP hnc hcZ hL hr3
  by_cases hp3 : p = 3
  · subst hp3
    exact hres X hKX hO hZ h5 P hP hZP hnc hcZ hL hr3
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  obtain ⟨K, hK⟩ := exists_component_of_not_isPConstrained hp hO hnc
  have hpZ := dvd_card_center_of_component hp hO hK (hcZ K hK)
  have hcat := (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.2 hKX).isCatalogGroup_center_quotient hK
  have h4 := hRank p hp hp5 ↥K hK.2.2 hcat hpZ
  obtain ⟨E, -, hEel, hEc⟩ := exists_elemAbelian_card_pow_of_le_pRank' h4
  set E' : Subgroup X := E.map K.subtype with hE'
  have hE'el : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hEel K.subtype
  have hE'c : Nat.card E' = p ^ 4 := by
    rw [hE', Subgroup.card_map_of_injective K.subtype_injective, hEc]
  have hE'L : E' ≤ CFSG.ComponentClassification.Layer.subgroup X :=
    (Subgroup.map_subtype_le E).trans (CFSG.ComponentClassification.Layer.component_le hK)
  obtain ⟨x, -, T, hTp, -, hPT, hE'T⟩ :=
    exists_conj_le_pGroup' (le_top : P ≤ ⊤) hP.2.1 (le_top : E' ≤ ⊤) hE'el.isPGroup
  have hTP : T = P := hP.2.2 T le_top hTp hPT
  rw [hTP] at hE'T
  haveI : (CFSG.ComponentClassification.Layer.subgroup X).Normal :=
    CFSG.ComponentClassification.Layer.normal X
  have hconjL : GLBConj x E' ≤ CFSG.ComponentClassification.Layer.subgroup X := by
    intro y hy
    rw [mem_gLBConj] at hy
    have h1 := (CFSG.ComponentClassification.Layer.normal X).conj_mem _ (hE'L hy) x⁻¹
    have e1 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [e1] at h1
  have hle : GLBConj x E' ≤
      P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore p X) :=
    le_inf hE'T (hconjL.trans le_sup_left)
  have h4' := CFSG.SectionRank.le_pRank hp.one_lt hle (Claims1211.isElemAbelian_gLBConj x hE'el)
    (by rw [Claims1211.card_gLBConj, hE'c])
  omega

theorem input24_5_of_residuals (hList : GL83.I243.PCoverList)
    (hSmall : GL83.I243.SmallThreeFacts) (hL4 : GL83.I243.LFourFacts)
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hRank : CFSG.LocalAnalysis.RankThreeTheoremC.SchurMultiplierRankFact)
    (hJ3 : CFSG.AGLEmbedding.KFactJ3OuterRank)
    (hSpo : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hON : Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group = 460815505920)
    (hComp : Input24_5_compCover) (hSm : Input24_5_smallThree) : Lemma1211.Input24_5 :=
  Inputs245.input24_5_of_inputs (input24_5_comp_of_cover hList hSmall hL4 hS hJ3 hSpo hON hComp)
    (input24_5_small_of_three hRank hSm)

section ThreeGroups

open scoped commutatorElement

theorem eq_one_of_fix_pair {V : Type} [Group V] {α : MulAut V} {v₀ v₁ : V}
    (htop : Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₀ = ⊤) (h₀ : α v₀ = v₀) (h₁ : α v₁ = v₁) :
    α = 1 := by
  have hle : Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₀ ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id V) :=
    sup_le ((Subgroup.zpowers_le).2 h₁) ((Subgroup.zpowers_le).2 h₀)
  rw [htop] at hle
  ext v
  exact hle (Subgroup.mem_top v)

theorem card_le_three_of_isPGroup_mulAut {V : Type} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ v : V, v ^ 3 = 1) (hV : Nat.card V ≤ 9)
    {S : Subgroup (MulAut V)} (hS : IsPGroup 3 S) : Nat.card S ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVp : IsPGroup 3 V := fun v => ⟨1, by rw [pow_one]; exact hexp v⟩
  have h2 : ∀ α ∈ S, α ^ 2 = 1 → α = 1 := by
    intro α hα h
    obtain ⟨k, hk⟩ := hS ⟨α, hα⟩
    have hk' : α ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : orderOf α ∣ Nat.gcd 2 (3 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one hk')
    have hg : Nat.gcd 2 (3 ^ k) = 1 := Nat.Coprime.pow_right _ (by norm_num)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  by_cases hV1 : Nat.card V = 1
  · have hsub : Subsingleton V := (Nat.card_eq_one_iff_unique.1 hV1).1
    have hS1 : ∀ α : MulAut V, α = 1 := fun α => MulEquiv.ext fun v => Subsingleton.elim _ _
    have : Nat.card S ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext ((hS1 a).trans (hS1 b).symm)⟩
    omega
  have hmod := hS.card_modEq_card_fixedPoints V
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hn1 : 1 ≤ n := by
    rcases n with _ | n
    · rw [pow_zero] at hn; exact absurd hn hV1
    · omega
  have hV3 : 3 ∣ Nat.card V := by rw [hn]; exact dvd_pow_self 3 (by omega)
  have hF3 : 3 ∣ Nat.card (MulAction.fixedPoints S V) :=
    (Nat.modEq_zero_iff_dvd.1 ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hV3))))
  have h1F : (1 : V) ∈ MulAction.fixedPoints S V := fun α => map_one (α : MulAut V)
  obtain ⟨v₀, hv₀F, hv₀1⟩ : ∃ v₀ ∈ MulAction.fixedPoints S V, v₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsub : MulAction.fixedPoints S V ⊆ {1} := fun v hv => hall v hv
    have hle : Nat.card (MulAction.fixedPoints S V) ≤ 1 := by
      have := Set.ncard_le_ncard hsub (Set.finite_singleton 1)
      rw [Set.ncard_singleton] at this
      rwa [← Nat.card_coe_set_eq] at this
    have hpos : 0 < Nat.card (MulAction.fixedPoints S V) :=
      Nat.card_pos_iff.2 ⟨⟨⟨1, h1F⟩⟩, Set.toFinite _⟩
    have := Nat.le_of_dvd hpos hF3
    omega
  have hfix₀ : ∀ α ∈ S, α v₀ = v₀ := fun α hα => hv₀F ⟨α, hα⟩
  have hv₀3 : orderOf v₀ = 3 := orderOf_eq_prime (hexp v₀) hv₀1
  have hZc : Nat.card (Subgroup.zpowers v₀) = 3 := by rw [Nat.card_zpowers, hv₀3]
  by_cases hcyc : ∀ v : V, v ∈ Subgroup.zpowers v₀
  · have hS1 : ∀ α ∈ S, α = 1 := by
      intro α hα
      have hle : Subgroup.zpowers v₀ ≤ MonoidHom.eqLocus (α : MulAut V).toMonoidHom (MonoidHom.id V) :=
        (Subgroup.zpowers_le).2 (hfix₀ α hα)
      ext v
      exact hle (hcyc v)
    have : Nat.card S ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext ((hS1 a a.2).trans (hS1 b b.2).symm)⟩
    omega
  push Not at hcyc
  obtain ⟨v₁, hv₁⟩ := hcyc
  have hcomm' : ∀ a ∈ Subgroup.zpowers v₀, a * v₁ = v₁ * a := fun a _ => hcomm a v₁
  have hsupc : Nat.card ↥(Subgroup.zpowers v₀ ⊔ Subgroup.zpowers v₁) = 3 * 3 := by
    rw [Inputs245.card_sup_zpowers Nat.prime_three (hexp v₁) hv₁ hcomm', hZc]
  have htop : Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₀ = ⊤ := by
    rw [sup_comm]
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    rw [hsupc]
    exact hV
  have hmem : ∀ α ∈ S, v₁⁻¹ * α v₁ ∈ Subgroup.zpowers v₀ := by
    intro α hα
    have hαv : α v₁ ∈ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₀ := htop ▸ Subgroup.mem_top _
    haveI hn0 : (Subgroup.zpowers v₀).Normal :=
      ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
    obtain ⟨h, hh, k, hk, hhk⟩ := Subgroup.mem_sup_of_normal_right.1 hαv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hv₁3 : orderOf v₁ = 3 :=
      orderOf_eq_prime (hexp v₁) (fun h1 => hv₁ (h1 ▸ Subgroup.one_mem _))
    have hi : v₁ ^ i = v₁ ^ ((i % 3 : ℤ)) := by
      rw [← zpow_mod_orderOf, hv₁3]
      rfl
    have hr : (i % 3 : ℤ) = 0 ∨ (i % 3 : ℤ) = 1 ∨ (i % 3 : ℤ) = 2 := by omega
    rcases hr with h0 | h1 | h2'
    · exfalso
      rw [hi, h0, zpow_zero, one_mul] at hhk
      apply hv₁
      have : α⁻¹ (α v₁) ∈ Subgroup.zpowers v₀ := by
        rw [← hhk]
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        rw [map_zpow]
        have : α⁻¹ v₀ = v₀ := by
          have := hfix₀ α⁻¹ (S.inv_mem hα)
          exact this
        rw [this]
        exact Subgroup.zpow_mem_zpowers v₀ j
      simpa using this
    · rw [hi, h1, zpow_one] at hhk
      rw [← hhk, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hk
    · exfalso
      rw [hi, h2'] at hhk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      have hsq : (α ^ 2) v₁ = v₁ := by
        rw [sq, MulAut.mul_apply, ← hhk, map_mul, map_zpow, map_zpow, ← hhk, hfix₀ α hα]
        have e1 : (v₁ ^ (2 : ℤ) * v₀ ^ j) ^ (2 : ℤ) * v₀ ^ j = v₁ ^ (4 : ℤ) * v₀ ^ (3 * j) := by
          rw [zpow_two (v₁ ^ (2 : ℤ) * v₀ ^ j)]
          have := hcomm (v₀ ^ j) (v₁ ^ (2 : ℤ))
          calc v₁ ^ (2 : ℤ) * v₀ ^ j * (v₁ ^ (2 : ℤ) * v₀ ^ j) * v₀ ^ j
              = v₁ ^ (2 : ℤ) * (v₀ ^ j * v₁ ^ (2 : ℤ)) * v₀ ^ j * v₀ ^ j := by group
            _ = v₁ ^ (2 : ℤ) * (v₁ ^ (2 : ℤ) * v₀ ^ j) * v₀ ^ j * v₀ ^ j := by rw [this]
            _ = v₁ ^ (4 : ℤ) * v₀ ^ (3 * j) := by group
        rw [e1]
        have e2 : v₁ ^ (4 : ℤ) = v₁ := by
          rw [show (4 : ℤ) = 1 + 3 by norm_num, zpow_add, zpow_one]
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hexp v₁, mul_one]
        have e3 : v₀ ^ (3 * j) = 1 := by
          rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hexp v₀, one_zpow]
        rw [e2, e3, mul_one]
      have hsq0 : (α ^ 2) v₀ = v₀ := by
        rw [sq, MulAut.mul_apply, hfix₀ α hα, hfix₀ α hα]
      have hα1 : α = 1 := h2 α hα (eq_one_of_fix_pair htop hsq0 hsq)
      apply hv₁
      have hv : v₁ = v₁ ^ (2 : ℤ) * v₀ ^ j := by rw [hhk, hα1, MulAut.one_apply]
      have : v₁⁻¹ = v₀ ^ j := by
        have e : v₁ ^ (2 : ℤ) = v₁ * v₁ := zpow_two v₁
        rw [e] at hv
        calc v₁⁻¹ = v₁⁻¹ * v₁⁻¹ * v₁ := by group
          _ = v₁⁻¹ * v₁⁻¹ * (v₁ * v₁ * v₀ ^ j) := by rw [← hv]
          _ = v₀ ^ j := by group
      have h' : v₁⁻¹ ∈ Subgroup.zpowers v₀ := this ▸ Subgroup.zpow_mem_zpowers v₀ j
      simpa using h'
  let f : S → Subgroup.zpowers v₀ := fun α => ⟨v₁⁻¹ * (α : MulAut V) v₁, hmem α α.2⟩
  have hf : Function.Injective f := by
    intro α β hαβ
    have h1 : (α : MulAut V) v₁ = (β : MulAut V) v₁ := by
      have := congrArg Subtype.val hαβ
      simpa [f] using this
    have hγ : (β : MulAut V)⁻¹ * α = 1 := by
      refine eq_one_of_fix_pair htop ?_ ?_
      · rw [MulAut.mul_apply, hfix₀ α α.2]
        exact hfix₀ _ (S.inv_mem β.2)
      · rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
    exact Subtype.ext (inv_mul_eq_one.1 hγ).symm
  calc Nat.card S ≤ Nat.card (Subgroup.zpowers v₀) := Nat.card_le_card_of_injective f hf
    _ = 3 := hZc

theorem card_le_nine_mul_commutator {X : Type} [Group X] [Finite X] {W : Subgroup X}
    (hexp : ∀ w ∈ W, w ^ 3 = 1) (hcl : ⁅W, W⁆ ≤ centerOf W)
    (hrk : ∀ U : Subgroup X, U ≤ W → IsElemAbelian 3 U → Nat.card U ≤ 9) :
    Nat.card W ≤ 9 * Nat.card ↥⁅W, W⁆ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW'pos : 1 ≤ Nat.card ↥⁅W, W⁆ := Nat.card_pos
  by_cases hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  · have hWe : IsElemAbelian 3 W := ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
    have := hrk W le_rfl hWe
    nlinarith
  push Not at hab
  obtain ⟨a, haW, b, hbW, hab⟩ := hab
  set Z : Subgroup X := centerOf W with hZdef
  have hZmem : ∀ z, z ∈ Z ↔ z ∈ W ∧ ∀ w ∈ W, w * z = z * w := fun z => Lemma1211.mem_centerOf_iff' W z
  have hZW : Z ≤ W := fun z hz => ((hZmem z).1 hz).1
  have hZel : IsElemAbelian 3 Z := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun z hz => hexp z (hZW hz)⟩
    exact ((hZmem _).1 x.2).2 _ (hZW y.2) |>.symm
  set c : X := ⁅a, b⁆ with hcdef
  have hcW' : c ∈ ⁅W, W⁆ := Subgroup.commutator_mem_commutator haW hbW
  have hc1 : c ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hcZ : c ∈ Z := hcl hcW'
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c (hZW hcZ)) hc1
  have hZ3 : 3 ≤ Nat.card Z := by
    have h := Subgroup.card_le_of_le ((Subgroup.zpowers_le).2 hcZ)
    rwa [Nat.card_zpowers, hc3] at h
  have haZ : a ∉ Z := fun h => hab (((hZmem a).1 h).2 b hbW).symm
  have hZa : ∀ z ∈ Z, z * a = a * z := fun z hz => (((hZmem z).1 hz).2 a haW).symm
  have hZaW : Z ⊔ Subgroup.zpowers a ≤ W := sup_le hZW ((Subgroup.zpowers_le).2 haW)
  have hZac : Nat.card ↥(Z ⊔ Subgroup.zpowers a) = Nat.card Z * 3 :=
    Inputs245.card_sup_zpowers Nat.prime_three (hexp a haW) haZ hZa
  have hZael : IsElemAbelian 3 (Z ⊔ Subgroup.zpowers a) :=
    Inputs245.isElemAbelian_sup_zpowers hZel (hexp a haW) hZa
  have hZle := hrk _ hZaW hZael
  rw [hZac] at hZle
  have hCa : Nat.card ↥(Subgroup.centralizer ({a} : Set X) ⊓ W) ≤ 9 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨x, hxC, hxn⟩ : ∃ x ∈ Subgroup.centralizer ({a} : Set X) ⊓ W,
        x ∉ Z ⊔ Subgroup.zpowers a := by
      by_contra hall
      push Not at hall
      have := Subgroup.card_le_of_le
        (fun y hy => hall y hy : Subgroup.centralizer ({a} : Set X) ⊓ W ≤ Z ⊔ Subgroup.zpowers a)
      omega
    have hxW : x ∈ W := hxC.2
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hxC.1
    have hcomm : ∀ y ∈ Z ⊔ Subgroup.zpowers a, y * x = x * y := by
      have hle : Z ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({x} : Set X) :=
        sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (((hZmem z).1 hz).2 x hxW).symm)
          ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hxa.symm))
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
    have hc' := Inputs245.card_sup_zpowers Nat.prime_three (hexp x hxW) hxn hcomm
    have hel' := Inputs245.isElemAbelian_sup_zpowers hZael (hexp x hxW) hcomm
    have hle' := hrk _ (sup_le hZaW ((Subgroup.zpowers_le).2 hxW)) hel'
    rw [hc', hZac] at hle'
    nlinarith
  set S : Set X := (fun w => w * a) '' ((⁅W, W⁆ : Subgroup X) : Set X) with hSdef
  have hSf : S.Finite := Set.toFinite _
  have hSconj : ∀ k ∈ W, k * a * k⁻¹ ∈ S := by
    intro k hk
    refine ⟨⁅k, a⁆, Subgroup.commutator_mem_commutator hk haW, ?_⟩
    show ⁅k, a⁆ * a = k * a * k⁻¹
    rw [commutatorElement_def]
    group
  have hidx := CFSG.LargeExtraspecial.GLR.relIndex_centralizer_le_ncard hSf hSconj
  have hSc : S.ncard = Nat.card ↥⁅W, W⁆ := by
    rw [hSdef, Set.ncard_image_of_injective _ (mul_left_injective a), ← Nat.card_coe_set_eq]
    rfl
  rw [hSc] at hidx
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({a} : Set X)) (K := W)
  calc Nat.card W = (Subgroup.centralizer ({a} : Set X)).relIndex W *
        Nat.card ↥(Subgroup.centralizer ({a} : Set X) ⊓ W) := h1.symm
    _ ≤ Nat.card ↥⁅W, W⁆ * 9 := Nat.mul_le_mul hidx hCa
    _ = 9 * Nat.card ↥⁅W, W⁆ := mul_comm _ _

end ThreeGroups

section TrivMod

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def trivMod (W : Subgroup X) (hW : W.Normal) : Subgroup X where
  carrier := {y | ∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆}
  one_mem' := fun w _ => by rw [commutatorElement_one_left]; exact Subgroup.one_mem _
  mul_mem' := by
    intro y z hy hz w hw
    have hn : (⁅W, W⁆).Normal := Subgroup.commutator_normal W W
    have e : ⁅y * z, w⁆ = (y * ⁅z, w⁆ * y⁻¹) * ⁅y, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hn.conj_mem _ (hz w hw) y) (hy w hw)
  inv_mem' := by
    intro y hy w hw
    have hw' : y⁻¹ * w * y ∈ W := by
      have := hW.conj_mem w hw y⁻¹
      rwa [inv_inv] at this
    have e : ⁅y⁻¹, w⁆ = (⁅y, y⁻¹ * w * y⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ (hy _ hw')

theorem mem_trivMod {W : Subgroup X} {hW : W.Normal} {y : X} :
    y ∈ trivMod W hW ↔ ∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆ :=
  Iff.rfl

theorem trivMod_normal (W : Subgroup X) (hW : W.Normal) : (trivMod W hW).Normal := by
  refine ⟨fun y hy g w hw => ?_⟩
  have hn : (⁅W, W⁆).Normal := Subgroup.commutator_normal W W
  have hw' : g⁻¹ * w * g ∈ W := by
    have := hW.conj_mem w hw g⁻¹
    rwa [inv_inv] at this
  have e : ⁅g * y * g⁻¹, w⁆ = g * ⁅y, g⁻¹ * w * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hn.conj_mem _ (hy _ hw') g

theorem card_le_three_mul_inf_trivMod {W : Subgroup X} (hW : W.Normal)
    (hexp : ∀ w ∈ W, w ^ 3 = 1) (hW9 : Nat.card W ≤ 9 * Nat.card ↥⁅W, W⁆)
    {E : Subgroup X} (hE : IsPGroup 3 E) : Nat.card E ≤ 3 * Nat.card ↥(E ⊓ trivMod W hW) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn' : (⁅W, W⁆).Normal := Subgroup.commutator_normal W W
  have hEN : E ≤ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hW]
    exact le_top
  set V := ↥W ⧸ _root_.commutator ↥W with hV
  let ρ : ↥E →* MulAut V :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (_root_.commutator ↥W)).comp
      (W.normalizerMonoidHom.comp (Subgroup.inclusion hEN))
  have hρ : ∀ (e : ↥E) (w : ↥W), ρ e (QuotientGroup.mk' _ w) =
      QuotientGroup.mk' _ ⟨(e : X) * w * (e : X)⁻¹, hW.conj_mem _ w.2 _⟩ := by
    intro e w
    simp only [ρ, MonoidHom.comp_apply]
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply]
    rfl
  have hVcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hVexp : ∀ v : V, v ^ 3 = 1 := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hexp x x.2)
    rw [this, map_one]
  have hVcard : Nat.card V ≤ 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator ↥W)
    have h2 : Nat.card ↥(_root_.commutator ↥W) = Nat.card ↥⁅W, W⁆ := by
      rw [← W.map_subtype_commutator, Subgroup.card_map_of_injective W.subtype_injective]
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥⁅W, W⁆ := Nat.card_pos
    by_contra hgt
    push Not at hgt
    have : 10 * Nat.card ↥⁅W, W⁆ ≤ Nat.card W := by
      rw [h1]
      exact Nat.mul_le_mul_right _ hgt
    omega
  have hrange : Nat.card ρ.range ≤ 3 := by
    haveI : Finite V := inferInstance
    have hp : IsPGroup 3 ρ.range := hE.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    exact card_le_three_of_isPGroup_mulAut hVcomm hVexp hVcard hp
  have hker : ρ.ker.map E.subtype ≤ E ⊓ trivMod W hW := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e.2, fun w hw => ?_⟩
    have h1 : ρ e (QuotientGroup.mk' _ ⟨w, hw⟩) = QuotientGroup.mk' _ ⟨w, hw⟩ := by
      rw [MonoidHom.mem_ker.1 he, MulAut.one_apply]
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 := Subgroup.mem_map_of_mem W.subtype h1
    rw [W.map_subtype_commutator] at h2
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h3 := hn'.conj_mem _ h2 ((e : X) * w * (e : X)⁻¹)
    have e3 : ((e : X) * w * (e : X)⁻¹) * (((e : X) * w * (e : X)⁻¹)⁻¹ * w) *
        ((e : X) * w * (e : X)⁻¹)⁻¹ = (⁅(e : X), w⁆)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e3] at h3
    have := Subgroup.inv_mem _ h3
    rwa [inv_inv] at this
  have hkc : Nat.card ρ.ker ≤ Nat.card ↥(E ⊓ trivMod W hW) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    exact Subgroup.card_le_of_le hker
  calc Nat.card E = Nat.card ρ.ker * Nat.card ρ.range := (Subgroup.card_ker_mul_card_range ρ).symm
    _ ≤ Nat.card ↥(E ⊓ trivMod W hW) * 3 := Nat.mul_le_mul hkc hrange
    _ = 3 * Nat.card ↥(E ⊓ trivMod W hW) := mul_comm _ _

end TrivMod

section Critical

open scoped commutatorElement
open CFSG.SectionRank.Ccomm (IsThompsonCritical)

variable {X : Type} [Group X] [Finite X]

theorem exists_pow_mem_centralizer_of_critical {O : Subgroup X} [O.Normal] (hO : IsPGroup 3 ↥O)
    {C : Subgroup ↥O} (hC : IsThompsonCritical C) {y : X}
    (hy : ∀ w ∈ (Claims1211b.omegaC 3 C).map (O.subtype.comp (MulEquiv.refl ↥O).toMonoidHom),
      ⁅y, w⁆ ∈ ⁅(Claims1211b.omegaC 3 C).map (O.subtype.comp (MulEquiv.refl ↥O).toMonoidHom),
        (Claims1211b.omegaC 3 C).map (O.subtype.comp (MulEquiv.refl ↥O).toMonoidHom)⁆) :
    ∃ a : ℕ, y ^ 3 ^ a ∈ Subgroup.centralizer (O : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e : ↥O ≃* ↥O := MulEquiv.refl ↥O with he
  set ψ : ↥O →* X := O.subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := O.subtype_injective.comp e.injective
  set WT := Claims1211b.omegaC 3 C with hWT
  haveI := hC.1
  haveI : (CFSG.omega₁ (G := ↥C) (p := 3)).Characteristic := CFSG.omega₁_characteristic _
  haveI : (⁅WT, WT⁆).Characteristic := inferInstance
  set α : MulAut ↥O := (e.trans (MulAut.conjNormal y)).trans e.symm with hα
  have hψα1 : ∀ t : ↥O, ψ (α t) = y * ψ t * y⁻¹ := by
    intro t
    simp [hψ, hα, MulAut.conjNormal_apply]
  have hψα : ∀ (n : ℕ) (t : ↥O), ψ ((α ^ n) t) = y ^ n * ψ t * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [pow_succ, MulAut.mul_apply, ih, hψα1, pow_succ]
      group
  have hα1 : ∀ w ∈ WT, w⁻¹ * α w ∈ ⁅WT, WT⁆ := by
    intro w hw
    have h1 := hy (ψ w⁻¹) (Subgroup.mem_map_of_mem ψ (WT.inv_mem hw))
    rw [← Subgroup.map_commutator] at h1
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 h1
    have h2 : ψ (w⁻¹ * α w) = (ψ c)⁻¹ := by
      rw [hce, map_mul, map_inv, hψα1, commutatorElement_def]
      group
    have h3 : w⁻¹ * α w = c⁻¹ := hψinj (by rw [h2, map_inv])
    rw [h3]
    exact Subgroup.inv_mem _ hc
  have hαn : ∀ (n : ℕ), ∀ w ∈ WT, w⁻¹ * (α ^ n) w ∈ ⁅WT, WT⁆ := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      rw [pow_succ, MulAut.mul_apply]
      have h1 := hα1 w hw
      have e1 : α w = w * (w⁻¹ * α w) := by group
      rw [e1, map_mul]
      have h2 : (α ^ n) (w⁻¹ * α w) ∈ ⁅WT, WT⁆ :=
        CFSG.SectionRank.Ccomm.char_apply_mem inferInstance (α ^ n) h1
      have e2 : w⁻¹ * ((α ^ n) w * (α ^ n) (w⁻¹ * α w)) =
          (w⁻¹ * (α ^ n) w) * (α ^ n) (w⁻¹ * α w) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (ih w hw) h2
  obtain ⟨a, b, hb, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos α).ne' 3 (by norm_num)
  have hβord : orderOf (α ^ (3 ^ a)) = b := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num)) ⟨b, hord⟩, hord,
      Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
  have hβ1 : α ^ (3 ^ a) = 1 := Claims1211b.aut_eq_one_of_critical (p := 3) (by norm_num) hO hC
    (α ^ (3 ^ a)) (by rw [hβord]; exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb).symm)
    (hαn (3 ^ a))
  refine ⟨a, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := hψα (3 ^ a) ⟨x, hx⟩
  rw [hβ1, MulAut.one_apply] at h1
  have hxt : ψ ⟨x, hx⟩ = x := rfl
  rw [hxt] at h1
  calc x * y ^ 3 ^ a = (y ^ 3 ^ a * x * (y ^ 3 ^ a)⁻¹) * y ^ 3 ^ a := by rw [← h1]
    _ = y ^ 3 ^ a * x := by group

theorem exists_kernel_of_rank_two {O : Subgroup X} [hOn : O.Normal] (hO : IsPGroup 3 ↥O)
    (hrk : ∀ U : Subgroup X, U ≤ O → IsElemAbelian 3 U → Nat.card U ≤ 9) :
    ∃ Q : Subgroup X, Q.Normal ∧ (∀ y ∈ Q, ∃ a : ℕ, y ^ 3 ^ a ∈ Subgroup.centralizer (O : Set X)) ∧
      ∀ E : Subgroup X, IsPGroup 3 ↥E → Nat.card E ≤ 3 * Nat.card ↥(E ⊓ Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨C, hC⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup hO
  set W : Subgroup X := (Claims1211b.omegaC 3 C).map (O.subtype.comp (MulEquiv.refl ↥O).toMonoidHom) with hWdef
  have hWn : W.Normal := Claims1211b.normal_omegaC_map (p := 3) (MulEquiv.refl ↥O) hC
  have hWO : W ≤ O := by
    rintro _ ⟨t, -, rfl⟩
    exact (t : ↥O).2
  have hexp : ∀ w ∈ W, w ^ 3 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, Claims1211b.pow_eq_one_of_mem_omegaC (p := 3) (by norm_num) hO hC ht, map_one]
  have hcl : ⁅W, W⁆ ≤ centerOf W := by
    rw [hWdef, ← Subgroup.map_commutator]
    exact (Subgroup.map_mono (Claims1211b.commutator_omegaC_le_center (p := 3) hC)).trans
      (Claims1211b.map_centerOf_le _ _)
  have hW9 := card_le_nine_mul_commutator hexp hcl (fun U hU hUe => hrk U (hU.trans hWO) hUe)
  refine ⟨trivMod W hWn, trivMod_normal W hWn, fun y hy => ?_, fun E hE =>
    card_le_three_mul_inf_trivMod hWn hexp hW9 hE⟩
  exact exists_pow_mem_centralizer_of_critical hO hC hy

end Critical

section SmallThreeProof

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem le_sup_of_pow_mem {p : ℕ} [Fact p.Prime] {P H N : Subgroup X} (hP : IsSylowIn p ⊤ P)
    [hH : H.Normal] [hN : N.Normal] (hpow : ∀ x ∈ H, ∃ k : ℕ, x ^ p ^ k ∈ N) :
    H ≤ (H ⊓ N) ⊔ (P ⊓ H) := by
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (Inputs245.sylowOf hP)
    hH.isSubnormal
  have hT' : (T : Subgroup ↥H).map H.subtype = P ⊓ H := hT
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  haveI : N'.Normal := Subgroup.Normal.subgroupOf hN H
  set M' : Subgroup ↥H := N' ⊔ (T : Subgroup ↥H) with hM'
  have h1 : M'.index ∣ (T : Subgroup ↥H).index := Subgroup.index_dvd_of_le le_sup_right
  have h2 : M'.index ∣ N'.index := Subgroup.index_dvd_of_le le_sup_left
  have hq : IsPGroup p (↥H ⧸ N') := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hpow x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    simpa using hk
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have h3 : N'.index = p ^ n := by rw [Subgroup.index, hn]
  have h4 : ¬ p ∣ (T : Subgroup ↥H).index := T.not_dvd_index
  rw [h3] at h2
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Fact.out).1 h2
  have hj0 : j = 0 := by
    by_contra hj0
    apply h4
    rw [hj'] at h1
    exact (dvd_pow_self p hj0).trans h1
  rw [hj0, pow_zero, Subgroup.index_eq_one] at hj'
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥H) ∈ M' := hj' ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem H.subtype hmem
  rw [hM', Subgroup.map_sup, hN', Subgroup.subgroupOf_map_subtype, hT', inf_comm N H] at this
  exact this

theorem exists_pow_mem_of_mem_sup {p : ℕ} {A P : Subgroup X} [hA : A.Normal] (hP : IsPGroup p ↥P)
    {x : X} (hx : x ∈ A ⊔ P) : ∃ k : ℕ, x ^ p ^ k ∈ A := by
  obtain ⟨g, hg, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (sup_comm A P ▸ hx)
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hgk : g ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff a).2 ha, mul_one, ← QuotientGroup.mk_pow, hgk, QuotientGroup.mk_one]

theorem layer_le_centralizer_pCore (p : ℕ) [Fact p.Prime] :
    CFSG.ComponentClassification.Layer.subgroup X ≤ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
  rw [← CFSG.layer_eq_componentClassification]
  exact Subgroup.le_centralizer_iff.1 (CFSG.WholeGroup.pCore_le_centralizer_layer p)

theorem sup_centralizer_inf_le {p : ℕ} [Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    (CFSG.ComponentClassification.Layer.subgroup X ⊔
        Subgroup.centralizer (CFSG.ComponentClassification.Layer.subgroup X : Set X)) ⊓
      Subgroup.centralizer (CFSG.pCore p X : Set X) ≤
    CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore p X := by
  set L := CFSG.ComponentClassification.Layer.subgroup X with hLdef
  haveI : L.Normal := CFSG.ComponentClassification.Layer.normal X
  have hLO := layer_le_centralizer_pCore (X := X) p
  rintro x ⟨hx, hxO⟩
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  have hcO : c ∈ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
    have h1 : l⁻¹ ∈ Subgroup.centralizer (CFSG.pCore p X : Set X) := Subgroup.inv_mem _ (hLO hl)
    have := Subgroup.mul_mem _ h1 hxO
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hF : c ∈ CFSG.generalizedFitting X := by
    refine CFSG.centralizer_generalizedFitting_le X ?_
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore X p hO, CFSG.layer_eq_componentClassification]
    have hle : CFSG.pCore p X ⊔ L ≤ Subgroup.centralizer ({c} : Set X) := by
      refine sup_le ?_ ?_
      · intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hcO) y hy)
      · intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hc) y hy)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
  rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore X p hO,
    CFSG.layer_eq_componentClassification] at hF
  have hF' : c ∈ L ⊔ CFSG.pCore p X := by rwa [sup_comm] at hF
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) hF'

theorem centerOf_le_pCore {p : ℕ} [Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : centerOf K ≤ CFSG.pCore p X := by
  have hc := CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot (G := X) p hO
  intro x hx
  obtain ⟨hxK, hxc⟩ := (Lemma1211.mem_centerOf_iff' K x).1 hx
  have hKL : K ≤ CFSG.layer X := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.component_le hK
  have hxC := CFSG.WholeGroup.mem_centralizer_layer_of_mem_component ((CFSG.isComponent_iff_open K).2 hK) hxK hxc
  refine hc ⟨⟨x, hKL hxK⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) g g.2)

theorem card_le_nine_of_le_pCore (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X}
    (hP : IsSylowIn 3 ⊤ P) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZK : Subgroup.center ↥K ≠ ⊥)
    (hr3 : CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3)
    {U : Subgroup X} (hUO : U ≤ CFSG.pCore 3 X) (hU : IsElemAbelian 3 U) : Nat.card U ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 3 X with hOdef
  set L := CFSG.ComponentClassification.Layer.subgroup X with hLdef
  obtain ⟨t, htPK, ht3, htC⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component Nat.prime_three (by norm_num) hO
      (Inputs245.sylowOf hP) hK
  have hpZ := dvd_card_center_of_component Nat.prime_three hO hK hZK
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hpZ
  set z' : X := ((w : ↥K) : X) with hz'
  have hz'3 : orderOf z' = 3 := by rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hz'K : z' ∈ K := (w : ↥K).2
  have hz'Z : z' ∈ centerOf K := ⟨w, w.2, rfl⟩
  have hz'O : z' ∈ O := centerOf_le_pCore hO hK hz'Z
  have hOP : O ≤ P := (CFSG.pCore_isPGroup (p := 3) (G := X)).le_sylow_of_normal (Inputs245.sylowOf hP)
  have hz'c : ∀ k ∈ K, k * z' = z' * k := fun k hk =>
    ((Lemma1211.mem_centerOf_iff' K z').1 hz'Z).2 k hk
  have htp : t ^ 3 = 1 := ht3 ▸ pow_orderOf_eq_one t
  have hz'p : z' ^ 3 = 1 := hz'3 ▸ pow_orderOf_eq_one z'
  have hz't : z' ∉ Subgroup.zpowers t := by
    intro h
    have hle : Subgroup.zpowers z' ≤ Subgroup.zpowers t := (Subgroup.zpowers_le).2 h
    have heq : Subgroup.zpowers z' = Subgroup.zpowers t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ht3, hz'3])
    have htz : t ∈ Subgroup.zpowers z' := heq ▸ Subgroup.mem_zpowers t
    apply htC
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 htz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Commute.zpow_right (hz'c k hk) i)).eq
  have htz'c : ∀ a ∈ Subgroup.zpowers t, a * z' = z' * a := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (hz'c t htPK.2) i)).eq
  set EK : Subgroup X := Subgroup.zpowers t ⊔ Subgroup.zpowers z' with hEK
  have hEKc : Nat.card EK = 9 := by
    rw [hEK, Inputs245.card_sup_zpowers Nat.prime_three hz'p hz't htz'c, Nat.card_zpowers, ht3]
  have hEKel : IsElemAbelian 3 EK :=
    Inputs245.isElemAbelian_sup_zpowers (Inputs245.isElemAbelian_zpowers' htp) hz'p htz'c
  have hEKK : EK ≤ K := sup_le ((Subgroup.zpowers_le).2 htPK.2) ((Subgroup.zpowers_le).2 hz'K)
  have hEKP : EK ≤ P := sup_le ((Subgroup.zpowers_le).2 htPK.1) ((Subgroup.zpowers_le).2 (hOP hz'O))
  have hEKO : Nat.card ↥(EK ⊓ O) ≤ 3 := by
    have hdvd : Nat.card ↥(EK ⊓ O) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hEKc]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases j
    · rw [hj']; norm_num
    · rw [hj']; norm_num
    · exfalso
      have heq : EK ⊓ O = EK :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj', hEKc]; norm_num)
      have htO : t ∈ O := ((heq.symm ▸ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t) : t ∈ EK)) :
        t ∈ EK ⊓ O).2
      apply htC
      have hKO := layer_le_centralizer_pCore (X := X) 3
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact ((Subgroup.mem_centralizer_iff.1 (hKO (CFSG.ComponentClassification.Layer.component_le hK hk)))
        t htO).symm
  have hcomm : ∀ h ∈ EK, ∀ u ∈ U, h * u = u * h := by
    intro h hh u hu
    have hKO := layer_le_centralizer_pCore (X := X) 3
    exact ((Subgroup.mem_centralizer_iff.1
      (hKO (CFSG.ComponentClassification.Layer.component_le hK (hEKK hh)))) u (hUO hu)).symm
  have hcard := Lemma1111.card_sup_mul_card_inf EK U hcomm
  have hinf : Nat.card ↥(EK ⊓ U) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf_left EK hUO)).trans hEKO
  have hel : IsElemAbelian 3 (EK ⊔ U) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hEKel hU
      (fun h hh => Subgroup.mem_centralizer_iff.2 fun u hu => (hcomm h hh u hu).symm)
  have hle : EK ⊔ U ≤ P ⊓ (L ⊔ O) :=
    sup_le (le_inf hEKP (hEKK.trans (CFSG.ComponentClassification.Layer.component_le hK) |>.trans
      le_sup_left)) (le_inf (hUO.trans hOP) (hUO.trans le_sup_right))
  have hrk := (CFSG.SectionRank.pRank_mono (by norm_num) hle).trans hr3
  have hcsup : Nat.card ↥(EK ⊔ U) ≤ 27 := by
    rw [GL83.PiGen.card_eq_pow_pRank hel]
    calc 3 ^ CFSG.Open.pRank 3 (EK ⊔ U) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 27 := by norm_num
  have hpos : 0 < Nat.card ↥(EK ⊓ U) := Nat.card_pos
  rw [hEKc] at hcard
  nlinarith

@[expose] def Input24_5_outClosed : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore 3 X = ⊥ → Subgroup.center X ≠ ⊥ → 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ P : Subgroup X, IsSylowIn 3 ⊤ P → IsCyclic ↥(centerOf P) →
      ¬ CFSG.ABGLocalTools.IsPConstrained 3 X →
      (∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥) →
      CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3 →
      (CFSG.ComponentClassification.Layer.subgroup X ⊔
        Subgroup.centralizer (CFSG.ComponentClassification.Layer.subgroup X : Set X) ⊔ P).Normal

theorem input24_5_smallThree_of_outClosed (hres : Input24_5_outClosed) : Input24_5_smallThree := by
  intro X _ _ hKX hO hZ h5 P hP hZP hnc hcZ hL hr3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := CFSG.ComponentClassification.Layer.subgroup X with hLdef
  set O := CFSG.pCore 3 X with hOdef
  haveI hLn : L.Normal := CFSG.ComponentClassification.Layer.normal X
  set A : Subgroup X := L ⊔ Subgroup.centralizer (L : Set X) with hAdef
  haveI hAn : A.Normal := Subgroup.sup_normal _ _
  haveI hX₁ : (A ⊔ P).Normal := hres X hKX hO hZ h5 P hP hZP hnc hcZ hr3
  have h4P : 4 ≤ CFSG.Open.pRank 3 P := by
    have := Inputs245.five_le_pRank_sylow hP h5
    omega
  have hPx : P ≤ Inputs245.x0 3 P :=
    Subgroup.le_normalizer.trans (Inputs245.normalizer_le_x0 le_rfl h4P)
  have hOP : O ≤ P :=
    (CFSG.pCore_isPGroup (p := 3) (G := X)).le_sylow_of_normal (Inputs245.sylowOf hP)
  have hLOx : L ⊔ O ≤ Inputs245.x0 3 P := sup_le hL (hOP.trans hPx)
  obtain ⟨K, hK⟩ := exists_component_of_not_isPConstrained Nat.prime_three hO hnc
  have hrkO : ∀ U : Subgroup X, U ≤ O → IsElemAbelian 3 U → Nat.card U ≤ 9 :=
    fun U hUO hU => card_le_nine_of_le_pCore hO hP hK (hcZ K hK) hr3 hUO hU
  haveI : O.Normal := CFSG.pCore_normal
  obtain ⟨Q, hQn, hQc, hQE⟩ :=
    exists_kernel_of_rank_two (O := O) (CFSG.pCore_isPGroup (p := 3) (G := X)) hrkO
  haveI := hQn
  obtain ⟨E, hEP, hEel, hEc⟩ := Claims1211b.exists_ekIn' hP h5
  have hEQ := hQE E hEel.isPGroup
  rw [hEc] at hEQ
  have hEQel : IsElemAbelian 3 (E ⊓ Q) := GL83.CompFam.elem_mono hEel inf_le_left
  obtain ⟨k, hk⟩ := hEQel.isPGroup.exists_card_eq
  have hk4 : 4 ≤ k := by
    rw [hk] at hEQ
    by_contra hlt
    push Not at hlt
    have : 3 * 3 ^ k ≤ 3 * 3 ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h35 : (3 : ℕ) ^ 5 = 243 := by norm_num
    have h33 : (3 : ℕ) ^ 3 = 27 := by norm_num
    omega
  have hPQ4 : 4 ≤ CFSG.Open.pRank 3 (P ⊓ Q) :=
    hk4.trans (CFSG.SectionRank.le_pRank (by norm_num) (inf_le_inf_right Q hEP) hEQel hk)
  set Q₁ : Subgroup X := Q ⊓ (A ⊔ P) with hQ₁def
  haveI hQ₁n : Q₁.Normal := Subgroup.normal_inf_normal Q (A ⊔ P)
  have hPQ₁ : P ⊓ Q₁ = P ⊓ Q := by
    rw [hQ₁def, ← inf_assoc, inf_right_comm, inf_eq_left.2 (le_sup_right : P ≤ A ⊔ P)]
  have hQ₁x : Q₁ ≤ Inputs245.x0 3 P := by
    set C₁ : Subgroup X := Q₁ ⊓ Subgroup.centralizer (O : Set X) with hC₁def
    haveI hC₁n : C₁.Normal := Subgroup.normal_inf_normal _ _
    have hQ₁le := le_sup_of_pow_mem hP (H := Q₁) (N := Subgroup.centralizer (O : Set X))
      (fun x hx => hQc x hx.1)
    have hC₁le := le_sup_of_pow_mem hP (H := C₁) (N := A)
      (fun x hx => exists_pow_mem_of_mem_sup hP.2.1 hx.1.2)
    have hC₁A : C₁ ⊓ A ≤ L ⊔ O := by
      intro x hx
      exact sup_centralizer_inf_le (X := X) (p := 3) hO ⟨hx.2, hx.1.2⟩
    have hC₁x : C₁ ≤ Inputs245.x0 3 P :=
      hC₁le.trans (sup_le (hC₁A.trans hLOx) (inf_le_left.trans hPx))
    exact hQ₁le.trans (sup_le hC₁x (inf_le_left.trans hPx))
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (Inputs245.sylowOf hP)
    hQ₁n.isSubnormal
  have hT' : (T : Subgroup ↥Q₁).map Q₁.subtype = P ⊓ Q₁ := hT
  have hF := Sylow.normalizer_sup_eq_top T
  rw [eq_top_iff, ← hF]
  refine sup_le ?_ hQ₁x
  have e : ((T : Subgroup ↥Q₁).map Q₁.subtype) = P ⊓ Q := by rw [hT', hPQ₁]
  rw [e]
  exact Inputs245.normalizer_le_x0 inf_le_left hPQ4

end SmallThreeProof

section OutClosed

variable {X : Type} [Group X] [Finite X]

theorem exists_e9_of_component (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X}
    (hP : IsSylowIn 3 ⊤ P) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZK : Subgroup.center ↥K ≠ ⊥) :
    ∃ E : Subgroup X, E ≤ P ⊓ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, htPK, ht3, htC⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component Nat.prime_three (by norm_num) hO
      (Inputs245.sylowOf hP) hK
  have hpZ := dvd_card_center_of_component Nat.prime_three hO hK hZK
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hpZ
  set z' : X := ((w : ↥K) : X) with hz'
  have hz'3 : orderOf z' = 3 := by rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hz'K : z' ∈ K := (w : ↥K).2
  have hz'Z : z' ∈ centerOf K := ⟨w, w.2, rfl⟩
  have hz'O : z' ∈ CFSG.pCore 3 X := centerOf_le_pCore hO hK hz'Z
  have hOP : CFSG.pCore 3 X ≤ P :=
    (CFSG.pCore_isPGroup (p := 3) (G := X)).le_sylow_of_normal (Inputs245.sylowOf hP)
  have hz'c : ∀ k ∈ K, k * z' = z' * k := fun k hk =>
    ((Lemma1211.mem_centerOf_iff' K z').1 hz'Z).2 k hk
  have htp : t ^ 3 = 1 := ht3 ▸ pow_orderOf_eq_one t
  have hz'p : z' ^ 3 = 1 := hz'3 ▸ pow_orderOf_eq_one z'
  have hz't : z' ∉ Subgroup.zpowers t := by
    intro h
    have hle : Subgroup.zpowers z' ≤ Subgroup.zpowers t := (Subgroup.zpowers_le).2 h
    have heq : Subgroup.zpowers z' = Subgroup.zpowers t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ht3, hz'3])
    have htz : t ∈ Subgroup.zpowers z' := heq ▸ Subgroup.mem_zpowers t
    apply htC
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 htz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Commute.zpow_right (hz'c k hk) i)).eq
  have htz'c : ∀ a ∈ Subgroup.zpowers t, a * z' = z' * a := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (hz'c t htPK.2) i)).eq
  set E : Subgroup X := Subgroup.zpowers t ⊔ Subgroup.zpowers z' with hE
  have hEc : Nat.card E = 9 := by
    rw [hE, Inputs245.card_sup_zpowers Nat.prime_three hz'p hz't htz'c, Nat.card_zpowers, ht3]
  refine ⟨E, le_inf (sup_le ((Subgroup.zpowers_le).2 htPK.1) ((Subgroup.zpowers_le).2 (hOP hz'O)))
    (sup_le ((Subgroup.zpowers_le).2 htPK.2) ((Subgroup.zpowers_le).2 hz'K)),
    Inputs245.isElemAbelian_sup_zpowers (Inputs245.isElemAbelian_zpowers' htp) hz'p htz'c, hEc, ?_⟩
  have hdvd : Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases j
  · rw [hj']; norm_num
  · rw [hj']; norm_num
  · exfalso
    have heq : E ⊓ Subgroup.centralizer (K : Set X) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj', hEc]; norm_num)
    exact htC ((heq.symm ▸ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t) : t ∈ E) :
      t ∈ E ⊓ Subgroup.centralizer (K : Set X)).2)

theorem false_of_three_components (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X}
    (hP : IsSylowIn 3 ⊤ P)
    (hr3 : CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3)
    (hcZ : ∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥)
    {K₁ K₂ K₃ : Subgroup X} (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤)
    (h₃ : IsComponentOf K₃ ⊤) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₁, hE₁, hE₁e, hE₁c, hE₁C⟩ := exists_e9_of_component hO hP h₁ (hcZ K₁ h₁)
  obtain ⟨E₂, hE₂, hE₂e, hE₂c, -⟩ := exists_e9_of_component hO hP h₂ (hcZ K₂ h₂)
  obtain ⟨E₃, hE₃, hE₃e, hE₃c, hE₃C⟩ := exists_e9_of_component hO hP h₃ (hcZ K₃ h₃)
  have c12 : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    Inputs245.comm_of_ne_component h₁ h₂ h12 (hE₁ ha).2 (hE₂ hb).2
  have hE₂C₁ : E₂ ≤ Subgroup.centralizer (K₁ : Set X) :=
    (hE₂.trans inf_le_right).trans (Inputs245.le_centralizer_of_ne_component h₁ h₂ h12.symm)
  have hE₁₃ : E₁ ≤ Subgroup.centralizer (K₃ : Set X) :=
    (hE₁.trans inf_le_right).trans (Inputs245.le_centralizer_of_ne_component h₃ h₁ h13)
  have hE₂₃ : E₂ ≤ Subgroup.centralizer (K₃ : Set X) :=
    (hE₂.trans inf_le_right).trans (Inputs245.le_centralizer_of_ne_component h₃ h₂ h23)
  have hcard12 := Lemma1111.card_sup_mul_card_inf E₁ E₂ c12
  have hinf12 : Nat.card ↥(E₁ ⊓ E₂) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf_left E₁ hE₂C₁)).trans hE₁C
  set E₁₂ := E₁ ⊔ E₂ with hE₁₂
  have hE₁₂e : IsElemAbelian 3 E₁₂ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hE₁e hE₂e
      (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (c12 a ha b hb).symm)
  have hE₁₂C : E₁₂ ≤ Subgroup.centralizer (K₃ : Set X) := sup_le hE₁₃ hE₂₃
  have c123 : ∀ a ∈ E₁₂, ∀ b ∈ E₃, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.1 (hE₁₂C ha)) b (hE₃ hb).2).symm
  have hcard123 := Lemma1111.card_sup_mul_card_inf E₁₂ E₃ c123
  have hinf123 : Nat.card ↥(E₁₂ ⊓ E₃) ≤ 3 := by
    rw [inf_comm]
    exact (Subgroup.card_le_of_le (inf_le_inf_left E₃ hE₁₂C)).trans hE₃C
  have hel : IsElemAbelian 3 (E₁₂ ⊔ E₃) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hE₁₂e hE₃e
      (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (c123 a ha b hb).symm)
  have hle : E₁₂ ⊔ E₃ ≤
      P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X) := by
    have hcomp : ∀ {K E : Subgroup X}, IsComponentOf K ⊤ → E ≤ P ⊓ K →
        E ≤ P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X) :=
      fun hK hE => le_inf (hE.trans inf_le_left)
        ((hE.trans inf_le_right).trans
          ((CFSG.ComponentClassification.Layer.component_le hK).trans le_sup_left))
    exact sup_le (sup_le (hcomp h₁ hE₁) (hcomp h₂ hE₂)) (hcomp h₃ hE₃)
  have hrk := (CFSG.SectionRank.pRank_mono (by norm_num) hle).trans hr3
  have hcsup : Nat.card ↥(E₁₂ ⊔ E₃) ≤ 27 := by
    rw [GL83.PiGen.card_eq_pow_pRank hel]
    calc 3 ^ CFSG.Open.pRank 3 (E₁₂ ⊔ E₃) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 27 := by norm_num
  have hpos12 : 0 < Nat.card ↥(E₁ ⊓ E₂) := Nat.card_pos
  have hpos123 : 0 < Nat.card ↥(E₁₂ ⊓ E₃) := Nat.card_pos
  rw [hE₁c, hE₂c] at hcard12
  rw [hE₃c] at hcard123
  have h27 : 27 ≤ Nat.card E₁₂ := by nlinarith
  nlinarith

theorem le_normalizer_of_rank (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X} (hP : IsSylowIn 3 ⊤ P)
    (hr3 : CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3)
    (hcZ : ∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : P ≤ Subgroup.normalizer (K : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro b hbP
  by_contra hbK
  set K₂ : Subgroup X := GLBConj b K with hK₂def
  set K₃ : Subgroup X := GLBConj b K₂ with hK₃def
  have hK₂ : IsComponentOf K₂ ⊤ := isComponentOf_gLBConj hK b
  have hK₃ : IsComponentOf K₃ ⊤ := isComponentOf_gLBConj hK₂ b
  have h12 : K ≠ K₂ := fun h => hbK (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  have h23 : K₂ ≠ K₃ := by
    intro h
    apply h12
    have := congrArg (GLBConj b⁻¹) h
    rwa [hK₃def, gLBConj_inv_gLBConj, hK₂def, gLBConj_inv_gLBConj] at this
  have h13 : K ≠ K₃ := by
    intro h
    apply hbK
    have hbb : b * b ∈ Subgroup.normalizer (K : Set X) := by
      rw [mem_normalizer_iff_gLBConj_eq, ← gLBConj_gLBConj]
      exact h.symm
    exact Inputs245.mem_of_mul_self_mem (by norm_num) hP.2.1 hbP hbb
  exact false_of_three_components hO hP hr3 hcZ hK hK₂ hK₃ h12 h13 h23

theorem exists_two_components (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X} (hP : IsSylowIn 3 ⊤ P)
    (hr3 : CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3)
    (hcZ : ∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥)
    (hnc : ¬ CFSG.ABGLocalTools.IsPConstrained 3 X) :
    ∃ K₁ K₂ : Subgroup X, IsComponentOf K₁ ⊤ ∧ IsComponentOf K₂ ⊤ ∧
      ∀ K : Subgroup X, IsComponentOf K ⊤ → K = K₁ ∨ K = K₂ := by
  obtain ⟨K₁, h₁⟩ := exists_component_of_not_isPConstrained Nat.prime_three hO hnc
  by_cases hall : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = K₁
  · exact ⟨K₁, K₁, h₁, h₁, fun K hK => Or.inl (hall K hK)⟩
  push Not at hall
  obtain ⟨K₂, h₂, h21⟩ := hall
  refine ⟨K₁, K₂, h₁, h₂, fun K hK => ?_⟩
  by_contra hne
  push Not at hne
  exact false_of_three_components hO hP hr3 hcZ h₁ h₂ hK (Ne.symm h21) (Ne.symm hne.1)
    (Ne.symm hne.2)

theorem pRank_component_le {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hr3 : CFSG.Open.pRank p (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore p X)) ≤ 3)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 3 := by
  by_contra h4
  push Not at h4
  obtain ⟨E, -, hEel, hEc⟩ := exists_elemAbelian_card_pow_of_le_pRank' (k := 4) h4
  set E' : Subgroup X := E.map K.subtype with hE'
  have hE'el : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hEel K.subtype
  have hE'c : Nat.card E' = p ^ 4 := by
    rw [hE', Subgroup.card_map_of_injective K.subtype_injective, hEc]
  have hE'L : E' ≤ CFSG.ComponentClassification.Layer.subgroup X :=
    (Subgroup.map_subtype_le E).trans (CFSG.ComponentClassification.Layer.component_le hK)
  obtain ⟨x, -, T, hTp, -, hPT, hE'T⟩ :=
    exists_conj_le_pGroup' (le_top : P ≤ ⊤) hP.2.1 (le_top : E' ≤ ⊤) hE'el.isPGroup
  have hTP : T = P := hP.2.2 T le_top hTp hPT
  rw [hTP] at hE'T
  have hconjL : GLBConj x E' ≤ CFSG.ComponentClassification.Layer.subgroup X := by
    intro y hy
    rw [mem_gLBConj] at hy
    have h1 := (CFSG.ComponentClassification.Layer.normal X).conj_mem _ (hE'L hy) x⁻¹
    have e1 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [e1] at h1
  have hle : GLBConj x E' ≤
      P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore p X) :=
    le_inf hE'T (hconjL.trans le_sup_left)
  have h4' := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hle
    (Claims1211.isElemAbelian_gLBConj x hE'el) (by rw [Claims1211.card_gLBConj, hE'c])
  omega

theorem mem_sup_centralizer_of_inner {K₁ K₂ : Subgroup X} (h₁ : IsComponentOf K₁ ⊤)
    (h₂ : IsComponentOf K₂ ⊤) {x k₁ k₂ : X} (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (hx₁ : ∀ y ∈ K₁, x * y * x⁻¹ = k₁ * y * k₁⁻¹) (hx₂ : ∀ y ∈ K₂, x * y * x⁻¹ = k₂ * y * k₂⁻¹) :
    x ∈ (K₁ ⊔ K₂) ⊔ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup X) : Set X) := by
  have hcen : ∀ c : X, (∀ y ∈ K₁, c * y * c⁻¹ = y) → (∀ y ∈ K₂, c * y * c⁻¹ = y) →
      c ∈ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup X) : Set X) := by
    intro c hc₁ hc₂
    have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({c} : Set X) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc y * c = (c * y * c⁻¹) * c := by rw [hc₁ y hy]
          _ = c * y := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc y * c = (c * y * c⁻¹) * c := by rw [hc₂ y hy]
          _ = c * y := by group
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  by_cases h12 : K₁ = K₂
  · subst h12
    have hc := hcen (k₁⁻¹ * x) (fun y hy => by rw [show k₁⁻¹ * x * y * (k₁⁻¹ * x)⁻¹ =
        k₁⁻¹ * (x * y * x⁻¹) * k₁ by group, hx₁ y hy]; group)
      (fun y hy => by rw [show k₁⁻¹ * x * y * (k₁⁻¹ * x)⁻¹ =
        k₁⁻¹ * (x * y * x⁻¹) * k₁ by group, hx₁ y hy]; group)
    have e : x = k₁ * (k₁⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk₁))
      (Subgroup.mem_sup_right hc)
  have hc₁₂ : ∀ y ∈ K₁, k₂ * y = y * k₂ := fun y hy =>
    Inputs245.comm_of_ne_component h₂ h₁ (Ne.symm h12) hk₂ hy
  have hc₂₁ : ∀ y ∈ K₂, k₁ * y = y * k₁ := fun y hy =>
    Inputs245.comm_of_ne_component h₁ h₂ h12 hk₁ hy
  have hc := hcen ((k₁ * k₂)⁻¹ * x)
    (fun y hy => by
      rw [show (k₁ * k₂)⁻¹ * x * y * ((k₁ * k₂)⁻¹ * x)⁻¹ =
        k₂⁻¹ * (k₁⁻¹ * (x * y * x⁻¹) * k₁) * k₂ by group, hx₁ y hy,
        show k₁⁻¹ * (k₁ * y * k₁⁻¹) * k₁ = y by group]
      calc k₂⁻¹ * y * k₂ = k₂⁻¹ * (k₂ * y) := by rw [hc₁₂ y hy]; group
        _ = y := by group)
    (fun y hy => by
      rw [show (k₁ * k₂)⁻¹ * x * y * ((k₁ * k₂)⁻¹ * x)⁻¹ =
        k₂⁻¹ * (k₁⁻¹ * (x * y * x⁻¹) * k₁) * k₂ by group, hx₂ y hy]
      have hz : k₂ * y * k₂⁻¹ ∈ K₂ := K₂.mul_mem (K₂.mul_mem hk₂ hy) (K₂.inv_mem hk₂)
      have e1 : k₁⁻¹ * (k₂ * y * k₂⁻¹) * k₁ = k₂ * y * k₂⁻¹ := by
        calc k₁⁻¹ * (k₂ * y * k₂⁻¹) * k₁ = k₁⁻¹ * (k₁ * (k₂ * y * k₂⁻¹)) := by
              rw [hc₂₁ _ hz]; group
          _ = k₂ * y * k₂⁻¹ := by group
      rw [e1]
      group)
  have e : x = (k₁ * k₂) * ((k₁ * k₂)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk₁)
    (Subgroup.mem_sup_right hk₂))) (Subgroup.mem_sup_right hc)

theorem le_sup_of_pow_mem' {p : ℕ} [Fact p.Prime] {P H N : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hPH : P ≤ H) [hN : N.Normal] (hpow : ∀ x ∈ H, ∃ k : ℕ, x ^ p ^ k ∈ N) : H ≤ N ⊔ P := by
  let T : Sylow p ↥H :=
    { toSubgroup := P.subgroupOf H
      isPGroup' := hP.2.1.comap_of_injective _ H.subtype_injective
      is_maximal' := by
        intro Q hQ hle
        have h1 : Q.map H.subtype = P := by
          refine hP.2.2 _ le_top (hQ.map _) ?_
          intro x hx
          exact ⟨⟨x, hPH hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        apply le_antisymm _ hle
        intro x hx
        rw [Subgroup.mem_subgroupOf, ← h1]
        exact ⟨x, hx, rfl⟩ }
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  haveI : N'.Normal := Subgroup.Normal.subgroupOf hN H
  set M' : Subgroup ↥H := N' ⊔ (T : Subgroup ↥H) with hM'
  have h1 : M'.index ∣ (T : Subgroup ↥H).index := Subgroup.index_dvd_of_le le_sup_right
  have h2 : M'.index ∣ N'.index := Subgroup.index_dvd_of_le le_sup_left
  have hq : IsPGroup p (↥H ⧸ N') := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hpow x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    simpa using hk
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have h3 : N'.index = p ^ n := by rw [Subgroup.index, hn]
  have h4 : ¬ p ∣ (T : Subgroup ↥H).index := T.not_dvd_index
  rw [h3] at h2
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Fact.out).1 h2
  have hj0 : j = 0 := by
    by_contra hj0
    apply h4
    rw [hj'] at h1
    exact (dvd_pow_self p hj0).trans h1
  rw [hj0, pow_zero, Subgroup.index_eq_one] at hj'
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥H) ∈ M' := hj' ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem H.subtype hmem
  rw [hM', Subgroup.map_sup, hN', Subgroup.subgroupOf_map_subtype] at this
  have hTm : (T : Subgroup ↥H).map H.subtype = P := by
    show (P.subgroupOf H).map H.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPH]
  rw [hTm] at this
  exact (sup_le_sup_right inf_le_left P) this

@[expose] def threeModInn (K : Type) [Group K]
    (h : ∀ α β : MulAut K, (∃ i : ℕ, α ^ 3 ^ i ∈ (MulAut.conj : K →* MulAut K).range) →
      (∃ j : ℕ, β ^ 3 ^ j ∈ (MulAut.conj : K →* MulAut K).range) →
      ∃ k : ℕ, (α * β) ^ 3 ^ k ∈ (MulAut.conj : K →* MulAut K).range) : Subgroup (MulAut K) where
  carrier := {α | ∃ i : ℕ, α ^ 3 ^ i ∈ (MulAut.conj : K →* MulAut K).range}
  one_mem' := ⟨0, by rw [one_pow]; exact Subgroup.one_mem _⟩
  mul_mem' := fun ha hb => h _ _ ha hb
  inv_mem' := by
    rintro α ⟨i, hi⟩
    exact ⟨i, by rw [inv_pow]; exact Subgroup.inv_mem _ hi⟩

theorem conj_mem_normalizer {K : Subgroup X} {g y : X}
    (hy : y ∈ Subgroup.normalizer ((GLBConj g K : Subgroup X) : Set X)) :
    g * y * g⁻¹ ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := (Subgroup.mem_normalizer_iff.1 hy) (g⁻¹ * z * g)
  rw [mem_gLBConj, mem_gLBConj] at h1
  have e1 : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
  have e2 : g * (y * (g⁻¹ * z * g) * y⁻¹) * g⁻¹ = g * y * g⁻¹ * z * (g * y * g⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

@[expose] def Input24_5_outThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    ∀ α β : MulAut K, (∃ i : ℕ, α ^ 3 ^ i ∈ (MulAut.conj : K →* MulAut K).range) →
      (∃ j : ℕ, β ^ 3 ^ j ∈ (MulAut.conj : K →* MulAut K).range) →
      ∃ k : ℕ, (α * β) ^ 3 ^ k ∈ (MulAut.conj : K →* MulAut K).range

theorem isCyclic_center_of_component (hT : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (hKX : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X}
    (hP : IsSylowIn 3 ⊤ P)
    (hr3 : CFSG.Open.pRank 3 (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore 3 X)) ≤ 3)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : IsCyclic (Subgroup.center ↥K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp := isPGroup_center_of_component Nat.prime_three hO hK
  have hrk := pRank_component_le hP hr3 hK
  have h1 : CFSG.Open.pRank 3 (Subgroup.center ↥K) ≤ 1 := by
    by_contra h2
    push Not at h2
    obtain ⟨-, -, h6, -⟩ := hT.T11 ↥K hK.2.2 (hKX.subgroup K) 3 Nat.prime_three (by norm_num) hZp h2
    omega
  refine SchurFacts2.isCyclic_center_of_card_roots_le Nat.prime_three hZp ?_
  let Ω : Subgroup ↥K :=
    { carrier := {k | k ∈ Subgroup.center ↥K ∧ k ^ 3 = 1}
      one_mem' := ⟨Subgroup.one_mem _, one_pow 3⟩
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        rw [(Commute.mul_pow (Subgroup.mem_center_iff.1 hb a)), ha3, hb3, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow, ha3, inv_one]⟩ }
  have hΩZ : Ω ≤ Subgroup.center ↥K := fun k hk => hk.1
  have hΩel : IsElemAbelian 3 Ω :=
    ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hΩZ b.2) a)⟩⟩, fun k hk => hk.2⟩
  have hΩc : Nat.card Ω ≤ 3 := by
    rw [GL83.PiGen.card_eq_pow_pRank hΩel]
    calc 3 ^ CFSG.Open.pRank 3 Ω ≤ 3 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) ((CFSG.SectionRank.pRank_mono (by norm_num) hΩZ).trans h1)
      _ = 3 := by norm_num
  have e : {z : Subgroup.center ↥K // z ^ 3 = 1} ≃ Ω :=
    { toFun := fun z => ⟨z.1, z.1.2, by simpa using congrArg Subtype.val z.2⟩
      invFun := fun k => ⟨⟨k.1, k.2.1⟩, Subtype.ext (by simpa using k.2.2)⟩
      left_inv := fun z => rfl
      right_inv := fun k => rfl }
  rw [Nat.card_congr e]
  exact hΩc

theorem input24_5_outClosed_of_outThree
    (hT : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112) (hres : Input24_5_outThree) :
    Input24_5_outClosed := by
  intro X _ _ hKX hO hZ h5 P hP hZP hnc hcZ hr3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K₁, K₂, h₁, h₂, hall⟩ := exists_two_components hO hP hr3 hcZ hnc
  set L := CFSG.ComponentClassification.Layer.subgroup X with hLdef
  have hL : L = K₁ ⊔ K₂ := by
    refine le_antisymm ?_ (sup_le (CFSG.ComponentClassification.Layer.component_le h₁)
      (CFSG.ComponentClassification.Layer.component_le h₂))
    rw [hLdef, CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    refine sSup_le fun K hK => ?_
    rcases hall K hK with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  haveI hLn : L.Normal := CFSG.ComponentClassification.Layer.normal X
  set A : Subgroup X := L ⊔ Subgroup.centralizer (L : Set X) with hAdef
  haveI hAn : A.Normal := Subgroup.sup_normal _ _
  have hP₁ := le_normalizer_of_rank hO hP hr3 hcZ h₁
  have hP₂ := le_normalizer_of_rank hO hP hr3 hcZ h₂
  have hcl : ∀ {K : Subgroup X}, IsComponentOf K ⊤ →
      ∀ α β : MulAut ↥K, (∃ i : ℕ, α ^ 3 ^ i ∈ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (∃ j : ℕ, β ^ 3 ^ j ∈ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ∃ k : ℕ, (α * β) ^ 3 ^ k ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun {K} hK =>
    hres ↥K hK.2.2
      ((CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.2 hKX).isCatalogGroup_center_quotient hK)
      (hcZ K hK) (isPGroup_center_of_component Nat.prime_three hO hK)
      (isCyclic_center_of_component hT hKX hO hP hr3 hK) (pRank_component_le hP hr3 hK)
  set N₁₂ : Subgroup X :=
    Subgroup.normalizer (K₁ : Set X) ⊓ Subgroup.normalizer (K₂ : Set X) with hN₁₂
  let ρ₁ : ↥N₁₂ →* MulAut ↥K₁ := K₁.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)
  let ρ₂ : ↥N₁₂ →* MulAut ↥K₂ := K₂.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  set T₁ := threeModInn ↥K₁ (hcl h₁) with hT₁
  set T₂ := threeModInn ↥K₂ (hcl h₂) with hT₂
  set Y : Subgroup X := ((T₁.comap ρ₁) ⊓ (T₂.comap ρ₂)).map N₁₂.subtype with hYdef
  have h3Y : ∀ x : ↥N₁₂, (∃ n : ℕ, (x : X) ^ 3 ^ n = 1) → (x : X) ∈ Y := by
    rintro x ⟨n, hn⟩
    have hx : x ^ 3 ^ n = 1 := Subtype.ext (by simpa using hn)
    refine ⟨x, ⟨⟨n, ?_⟩, ⟨n, ?_⟩⟩, rfl⟩
    · show (ρ₁ x) ^ 3 ^ n ∈ (MulAut.conj : ↥K₁ →* MulAut ↥K₁).range
      rw [← map_pow, hx, map_one]
      exact Subgroup.one_mem _
    · show (ρ₂ x) ^ 3 ^ n ∈ (MulAut.conj : ↥K₂ →* MulAut ↥K₂).range
      rw [← map_pow, hx, map_one]
      exact Subgroup.one_mem _
  have hPY : P ≤ Y := by
    intro y hy
    obtain ⟨k, hk⟩ := hP.2.1 ⟨y, hy⟩
    exact h3Y ⟨y, hP₁ hy, hP₂ hy⟩ ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hYA : ∀ y ∈ Y, ∃ k : ℕ, y ^ 3 ^ k ∈ A := by
    rintro _ ⟨x, ⟨⟨i, hi⟩, ⟨j, hj⟩⟩, rfl⟩
    refine ⟨i + j, ?_⟩
    have hi' : ρ₁ (x ^ 3 ^ (i + j)) ∈ (MulAut.conj : ↥K₁ →* MulAut ↥K₁).range := by
      rw [map_pow, pow_add, pow_mul]
      exact Subgroup.pow_mem _ hi _
    have hj' : ρ₂ (x ^ 3 ^ (i + j)) ∈ (MulAut.conj : ↥K₂ →* MulAut ↥K₂).range := by
      rw [map_pow, pow_add, mul_comm (3 ^ i), pow_mul]
      exact Subgroup.pow_mem _ hj _
    obtain ⟨k₁, hk₁⟩ := hi'
    obtain ⟨k₂, hk₂⟩ := hj'
    have hx₁ : ∀ y ∈ K₁, ((x ^ 3 ^ (i + j) : ↥N₁₂) : X) * y * ((x ^ 3 ^ (i + j) : ↥N₁₂) : X)⁻¹ =
        (k₁ : X) * y * (k₁ : X)⁻¹ := by
      intro y hy
      have h := congrArg (fun φ : MulAut ↥K₁ => ((φ ⟨y, hy⟩ : ↥K₁) : X)) hk₁
      have h2 : ((ρ₁ (x ^ 3 ^ (i + j))) ⟨y, hy⟩ : X) =
          ((x ^ 3 ^ (i + j) : ↥N₁₂) : X) * y * ((x ^ 3 ^ (i + j) : ↥N₁₂) : X)⁻¹ := rfl
      rw [← h2, ← h, MulAut.conj_apply]
      rfl
    have hx₂ : ∀ y ∈ K₂, ((x ^ 3 ^ (i + j) : ↥N₁₂) : X) * y * ((x ^ 3 ^ (i + j) : ↥N₁₂) : X)⁻¹ =
        (k₂ : X) * y * (k₂ : X)⁻¹ := by
      intro y hy
      have h := congrArg (fun φ : MulAut ↥K₂ => ((φ ⟨y, hy⟩ : ↥K₂) : X)) hk₂
      have h2 : ((ρ₂ (x ^ 3 ^ (i + j))) ⟨y, hy⟩ : X) =
          ((x ^ 3 ^ (i + j) : ↥N₁₂) : X) * y * ((x ^ 3 ^ (i + j) : ↥N₁₂) : X)⁻¹ := rfl
      rw [← h2, ← h, MulAut.conj_apply]
      rfl
    have hmem := mem_sup_centralizer_of_inner h₁ h₂ k₁.2 k₂.2 hx₁ hx₂
    rw [← hL] at hmem
    simpa using hmem
  have hYle : Y ≤ A ⊔ P := le_sup_of_pow_mem' hP hPY hYA
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (sup_comm A P ▸ hx)
  have hgy : g * y * g⁻¹ ∈ Y := by
    have hN : ∀ {K : Subgroup X}, IsComponentOf K ⊤ → g * y * g⁻¹ ∈ Subgroup.normalizer (K : Set X) := by
      intro K hK
      refine conj_mem_normalizer ?_
      rcases hall _ (isComponentOf_gLBConj hK g) with h | h <;> rw [h]
      · exact hP₁ hy
      · exact hP₂ hy
    obtain ⟨k, hk⟩ := hP.2.1 ⟨y, hy⟩
    have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine h3Y ⟨g * y * g⁻¹, hN h₁, hN h₂⟩ ⟨k, ?_⟩
    show (g * y * g⁻¹) ^ 3 ^ k = 1
    rw [conj_pow, hyk, mul_one, mul_inv_cancel]
  have e : g * (y * a) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hYle hgy) (Subgroup.mem_sup_left (hAn.conj_mem a ha g))

theorem input24_5_of_comp_out (hList : GL83.I243.PCoverList)
    (hSmall : GL83.I243.SmallThreeFacts) (hL4 : GL83.I243.LFourFacts)
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hRank : CFSG.LocalAnalysis.RankThreeTheoremC.SchurMultiplierRankFact)
    (hT : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (hJ3 : CFSG.AGLEmbedding.KFactJ3OuterRank)
    (hSpo : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hON : Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group = 460815505920)
    (hComp : Input24_5_compCover) (hOut : Input24_5_outThree) : Lemma1211.Input24_5 :=
  input24_5_of_residuals hList hSmall hL4 hS hRank hJ3 hSpo hON hComp
    (input24_5_smallThree_of_outClosed (input24_5_outClosed_of_outThree hT hOut))

theorem threeMod_closed_of_outTwo {K : Type} [Group K] (hOut : CFSG.AGLEmbedding.KOutTwoGroup K)
    (α β : MulAut K) (hα : ∃ i : ℕ, α ^ 3 ^ i ∈ (MulAut.conj : K →* MulAut K).range)
    (hβ : ∃ j : ℕ, β ^ 3 ^ j ∈ (MulAut.conj : K →* MulAut K).range) :
    ∃ k : ℕ, (α * β) ^ 3 ^ k ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨i, hi⟩ := hα
  obtain ⟨j, hj⟩ := hβ
  obtain ⟨k, hk⟩ := hOut α
  obtain ⟨l, hl⟩ := hOut β
  refine ⟨0, ?_⟩
  rw [pow_zero, pow_one]
  exact Subgroup.mul_mem _ (mem_inner_of_pow_mem hi hk) (mem_inner_of_pow_mem hj hl)

theorem threeMod_closed_of_normalSylow {K : Type} [Group K] [Finite K]
    (h : CFSG.AGLEmbedding.KOutNormalSylow 3 K) (α β : MulAut K)
    (hα : ∃ i : ℕ, α ^ 3 ^ i ∈ (MulAut.conj : K →* MulAut K).range)
    (hβ : ∃ j : ℕ, β ^ 3 ^ j ∈ (MulAut.conj : K →* MulAut K).range) :
    ∃ k : ℕ, (α * β) ^ 3 ^ k ∈ (MulAut.conj : K →* MulAut K).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun β : MulAut K => (β : K → K)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨S⟩ : Nonempty (Sylow 3 (MulAut K)) := inferInstance
  set I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hI
  haveI hIn : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K
  set N : Subgroup (MulAut K) := I ⊔ (S : Subgroup (MulAut K)) with hNdef
  haveI hN : N.Normal := h S
  have key : ∀ γ : MulAut K, (∃ i : ℕ, γ ^ 3 ^ i ∈ I) → γ ∈ N := by
    rintro γ ⟨i, hi⟩
    have h1 : (QuotientGroup.mk γ : MulAut K ⧸ N) ^ 3 ^ i = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_sup_left hi
    have h2 : orderOf (QuotientGroup.mk γ : MulAut K ⧸ N) ∣ N.index := by
      rw [Subgroup.index]
      exact orderOf_dvd_natCard _
    have h3 : N.index ∣ (S : Subgroup (MulAut K)).index := Subgroup.index_dvd_of_le le_sup_right
    have h4 : ¬ 3 ∣ (S : Subgroup (MulAut K)).index := S.not_dvd_index
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h1)
    have hj0 : j = 0 := by
      by_contra hj0
      apply h4
      rw [hj] at h2
      exact (dvd_pow_self 3 hj0).trans (h2.trans h3)
    rw [hj0, pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hj
    exact hj
  exact exists_pow_mem_of_mem_sup S.isPGroup' (Subgroup.mul_mem _ (key α hα) (key β hβ))

theorem input24_5_outThree_holds (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide)
    (hSmall : GL83.I243.SmallThreeFacts)
    (hSpo : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hSL3 : CFSG.LocalAnalysis.RankThreeTheoremC.KFactSL3OutNormalSylow) : Input24_5_outThree := by
  intro K _ _ hq hcat hZ hZp hZc hrk α β hα hβ
  rcases hW K hq hcat hZ hZp hZc hrk with h6 | h7 | h22 | hON | ⟨d, hd, he⟩
  · have h56 : 5 ≤ 6 := by norm_num
    obtain ⟨e⟩ := h6
    obtain ⟨hOut, -, -⟩ := hSmall K hq (.alternating 6 h56)
      (Or.inl ⟨6, h56, Or.inl rfl, rfl⟩) ⟨e⟩
    exact threeMod_closed_of_outTwo hOut α β hα hβ
  · have h57 : 5 ≤ 7 := by norm_num
    obtain ⟨e⟩ := h7
    obtain ⟨hOut, -, -⟩ := hSmall K hq (.alternating 7 h57)
      (Or.inl ⟨7, h57, Or.inr rfl, rfl⟩) ⟨e⟩
    exact threeMod_closed_of_outTwo hOut α β hα hβ
  · obtain ⟨hOut, -, -⟩ := hSmall K hq (.sporadic .M22) (Or.inr rfl) h22
    exact threeMod_closed_of_outTwo hOut α β hα hβ
  · haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
    have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
    have hle := hSpo (K ⧸ Subgroup.center K) inferInstance hnab .ONan hON
    exact threeMod_closed_of_outTwo (CFSG.AGLEmbedding.kOutTwoGroup_of_card_outer_le_two hq hle)
      α β hα hβ
  · exact threeMod_closed_of_normalSylow (hSL3 K hq d hd he) α β hα hβ

theorem input24_5_of_comp (hList : GL83.I243.PCoverList)
    (hSmall : GL83.I243.SmallThreeFacts) (hL4 : GL83.I243.LFourFacts)
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hRank : CFSG.LocalAnalysis.RankThreeTheoremC.SchurMultiplierRankFact)
    (hT : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide)
    (hSpo : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hSL3 : CFSG.LocalAnalysis.RankThreeTheoremC.KFactSL3OutNormalSylow)
    (hJ3 : CFSG.AGLEmbedding.KFactJ3OuterRank)
    (hON : Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group = 460815505920)
    (hComp : Input24_5_compCover) : Lemma1211.Input24_5 :=
  input24_5_of_comp_out hList hSmall hL4 hS hRank hT hJ3 hSpo hON hComp
    (input24_5_outThree_holds hW hSmall hSpo hSL3)

end OutClosed

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245b

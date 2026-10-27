module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import Certificates.Certificate129020
public import CFSG.Sporadic.HN.F5Group

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Certificates.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem two_pow_le_index_sq_of_psiAut {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} {S : Type} [Group S] (e : CQ L ≃* S)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {b : MulAut W} (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1)
    {x y : Fin (n + 1) → S} {z : S} (h : HeisCfg p (n + 1) x y z) (hy : ∀ i, y i ^ p = 1)
    (hinv : psiAut L e hb (x 0) = (x 0)⁻¹) :
    2 ^ ((p - 1) * p ^ n * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers b)).index ^ 2 := by
  let π : ↥L →* S := (e : CQ L →* S).comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : ∀ l : ↥L, π l = e (QuotientGroup.mk l) := fun _ => rfl
  have hK : π.ker = Subgroup.center ↥L := by
    ext k
    rw [MonoidHom.mem_ker, hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hKp : ¬ p ∣ Nat.card π.ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', hx'1, -, -, -⟩ := HeisCfg.exists_lift π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hK.le hKp h hy
  have hc : conjAut L hb (x' 0) = (x' 0)⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one π hK.le hKp ?_ ?_ ?_
    · rw [← map_pow, h'.xp 0, map_one]
    · rw [inv_pow, h'.xp 0, inv_one]
    · have h1 : π (conjAut L hb (x' 0)) = psiAut L e hb (π (x' 0)) := by
        rw [hπ, hπ, psiAut_mk]
      rw [h1, hx'1, hinv, map_inv, hx'1]
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : b * L.subtype (x' 0) * b⁻¹ = (L.subtype (x' 0))⁻¹ := by
    have h2 := congrArg Subtype.val hc
    rw [coe_conjAut] at h2
    simpa using h2
  exact two_pow_le_index_sq_of_heisCfg hW hp2 (h'.map L.subtype hz') hb2 hinv'

noncomputable def mclTau (c : ℕ) : Equiv.Perm (Fin 275) :=
  if c = 0 then mclGen 0 else tp 275 (mclCentTbl 17)

noncomputable def mclX (c : ℕ) : Equiv.Perm (Fin 275) := tp 275 (mclHeisTbl (2 * c))

noncomputable def mclY (c : ℕ) : Equiv.Perm (Fin 275) := tp 275 (mclHeisTbl (2 * c + 1))

noncomputable def mclW (c : ℕ) : Equiv.Perm (Fin 275) := (mclX c)⁻¹ * (mclY c)⁻¹ * mclX c * mclY c

theorem mclHeis_parts :
    permOK 275 (mclCentTbl 17) = true ∧ mclHeisOK 0 = true ∧ mclHeisOK 1 = true := by
  have h := Certificates.certificate129020
  unfold mclHeisCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem rep_mclHeisTau
    (c : ℕ) : Rep 275 (mclHeisTau c) (mclTau c) := by
  unfold mclHeisTau mclTau
  split_ifs
  · exact mcl_groupData.rep 0 (by rw [show mclPGTbls.size = 2 from rfl]; norm_num)
  · exact rep_tp mclHeis_parts.1

theorem mclOuterRep_facts :
    tp 275 (mclCentTbl 17) * tp 275 (mclCentTbl 17) = 1 ∧ tp 275 (mclCentTbl 17) ∉ mclP := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨-, h2, h3, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at h2 h3
  refine ⟨?_, h3.1 rfl⟩
  rw [← sq, ← h2]
  exact pow_orderOf_eq_one _

theorem mclTau_mul_self
    (c : ℕ) : mclTau c * mclTau c = 1 := by
  unfold mclTau
  split_ifs
  · rw [← sq, ← mcl_word_orders.1]
    exact pow_orderOf_eq_one _
  · exact mclOuterRep_facts.1

theorem mclHeis_facts
    {c : ℕ} (hc : c = 0 ∨ c = 1) :
    mclX c ∈ mclP ∧ mclY c ∈ mclP ∧ mclX c ^ 5 = 1 ∧ mclY c ^ 5 = 1 ∧ mclW c ^ 5 = 1 ∧
      mclW c ≠ 1 ∧ mclX c * mclW c = mclW c * mclX c ∧ mclY c * mclW c = mclW c * mclY c ∧
      mclTau c * mclX c * mclTau c = (mclX c)⁻¹ := by
  have h : mclHeisOK c = true := by
    rcases hc with rfl | rfl
    · exact mclHeis_parts.2.1
    · exact mclHeis_parts.2.2
  simp only [mclHeisOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpX, hpY⟩, hiX⟩, hiY⟩, hsX⟩, hsY⟩, h5X⟩, h5Y⟩, h5W⟩, hW1⟩, hcX⟩, hcY⟩,
    hτ⟩ := h
  have hn : 275 < 2 ^ 32 := by norm_num
  have rX : Rep 275 (mclHeisTbl (2 * c)) (mclX c) := rep_tp hpX
  have rY : Rep 275 (mclHeisTbl (2 * c + 1)) (mclY c) := rep_tp hpY
  have rXi := rep_invT rX hiX
  have rYi := rep_invT rY hiY
  have rW : Rep 275 (mclHeisW c) (mclW c) := ((rXi.compT rYi).compT rX).compT rY
  refine ⟨(mcl_groupData.sift _ _ rX).1 hsX, (mcl_groupData.sift _ _ rY).1 hsY,
    (tblEq_idT_iff hn (rX.powT hn 5)).1 h5X, (tblEq_idT_iff hn (rY.powT hn 5)).1 h5Y,
    (tblEq_idT_iff hn (rW.powT hn 5)).1 h5W, fun h1 => ?_,
    (tblEq_iff_eq (rX.compT rW) (rW.compT rX)).1 hcX,
    (tblEq_iff_eq (rY.compT rW) (rW.compT rY)).1 hcY,
    (tblEq_iff_eq (((rep_mclHeisTau c).compT rX).compT (rep_mclHeisTau c)) rXi).1 hτ⟩
  rw [(tblEq_idT_iff hn rW).2 h1] at hW1
  exact Bool.noConfusion hW1

theorem mcl_heisP
    {c : ℕ} (hc : c = 0 ∨ c = 1) {g : Equiv.Perm (Fin 275)} (hg : g ∈ mclP) :
    ∃ X' Y' W' : mclP, HeisCfg 5 1 (fun _ => X') (fun _ => Y') W' ∧ Y' ^ 5 = 1 ∧
      g * mclTau c * g⁻¹ * (X' : Equiv.Perm (Fin 275)) * (g * mclTau c * g⁻¹)⁻¹ =
        (X' : Equiv.Perm (Fin 275))⁻¹ := by
  obtain ⟨hXP, hYP, hX5, hY5, hW5, hW1, hXW, hYW, hτX⟩ := mclHeis_facts hc
  have hWP : mclW c ∈ mclP := by
    unfold mclW
    exact mclP.mul_mem (mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hXP) (mclP.inv_mem hYP)) hXP) hYP
  have hc' : ∀ {a : Equiv.Perm (Fin 275)}, a ∈ mclP → g * a * g⁻¹ ∈ mclP := fun ha =>
    mclP.mul_mem (mclP.mul_mem hg ha) (mclP.inv_mem hg)
  refine ⟨⟨g * mclX c * g⁻¹, hc' hXP⟩, ⟨g * mclY c * g⁻¹, hc' hYP⟩, ⟨g * mclW c * g⁻¹, hc' hWP⟩,
    ?_, ?_, ?_⟩
  · exact
      { xp := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, hX5]; group)
        zp := Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, hW5]; group)
        zx := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          calc g * mclX c * g⁻¹ * (g * mclW c * g⁻¹) = g * (mclX c * mclW c) * g⁻¹ := by group
            _ = g * (mclW c * mclX c) * g⁻¹ := by rw [hXW]
            _ = g * mclW c * g⁻¹ * (g * mclX c * g⁻¹) := by group)
        zy := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          calc g * mclY c * g⁻¹ * (g * mclW c * g⁻¹) = g * (mclY c * mclW c) * g⁻¹ := by group
            _ = g * (mclW c * mclY c) * g⁻¹ := by rw [hYW]
            _ = g * mclW c * g⁻¹ * (g * mclY c * g⁻¹) := by group)
        yx := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          unfold mclW
          group)
        xx := fun _ _ => rfl
        yy := fun i j hij => absurd (Subsingleton.elim i j) hij
        xy := fun i j hij => absurd (Subsingleton.elim i j) hij
        z1 := fun h1 => hW1 (by
          have h2 := congrArg (fun x : mclP => g⁻¹ * (x : Equiv.Perm (Fin 275)) * g) h1
          simpa [mul_assoc] using h2) }
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, hY5]
    group
  · have hτi : (mclTau c)⁻¹ = mclTau c := inv_eq_of_mul_eq_one_right (mclTau_mul_self c)
    calc g * mclTau c * g⁻¹ * (g * mclX c * g⁻¹) * (g * mclTau c * g⁻¹)⁻¹
        = g * (mclTau c * mclX c * (mclTau c)⁻¹) * g⁻¹ := by group
      _ = g * (mclX c)⁻¹ * g⁻¹ := by rw [hτi, hτX]
      _ = (g * mclX c * g⁻¹)⁻¹ := by group

theorem mcl_heisGen :
    ∀ t : ↥mclP, t * t = 1 → t ≠ 1 →
      ∃ (x y : Fin (0 + 1) → ↥mclP) (z : ↥mclP),
        HeisCfg 5 (0 + 1) x y z ∧ (∀ i, y i ^ 5 = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹ := by
  intro t ht2 ht1
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq, ht2]) ht1
  obtain ⟨g, hg⟩ := mcl_involution_conj_a hord
  obtain ⟨X', Y', W', hP, hY5, hinv⟩ := mcl_heisP (Or.inl rfl) g.2
  refine ⟨fun _ => X', fun _ => Y', W', hP, fun _ => hY5, ?_⟩
  apply Subtype.ext
  have ht : (t : Equiv.Perm (Fin 275)) = g * mclTau 0 * (g : Equiv.Perm (Fin 275))⁻¹ := by
    rw [hg]
    simp [mclTau, mcla0]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [ht]
  exact hinv

theorem mcl_outer_heis :
    ∀ ψ : MulAut ↥mclP, ψ ∉ (MulAut.conj : ↥mclP →* MulAut ↥mclP).range → ψ * ψ = 1 →
      ∃ (x y : Fin (0 + 1) → ↥mclP) (z : ↥mclP),
        HeisCfg 5 (0 + 1) x y z ∧ (∀ i, y i ^ 5 = 1) ∧ ψ (x 0) = (x 0)⁻¹ := by
  intro ψ hψ hψ2
  obtain ⟨eR, heR, himage, -, -⟩ := mcl_full_automorphism_model
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨x, rfl⟩ := eR.surjective ψ
  have hxP : (x : Equiv.Perm (Fin 275)) ∉ mclP := by
    intro hx
    apply hψ
    have hmem : eR x ∈ (mclP.subgroupOf mclR).map eR.toMonoidHom :=
      ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [himage] at hmem
    exact hmem
  have hx2 : x * x = 1 := eR.injective (by rw [map_mul, hψ2, map_one])
  have hx1 : (x : Equiv.Perm (Fin 275)) ≠ 1 := fun h => hxP (h ▸ mclP.one_mem)
  have hxord : orderOf (x : Equiv.Perm (Fin 275)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, hx2, Subgroup.coe_one]) hx1
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x x.2 hxord
  have hrP : tp 275 r.rep ∉ mclP := by
    intro h
    apply hxP
    rw [hxg]
    exact mclP.mul_mem (mclP.mul_mem hg h) (mclP.inv_mem hg)
  have hout : r.outer = true := ((hrows r hr).2.2.1).2 hrP
  have hrep : r.rep = mclCentTbl 17 := by
    simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact absurd hout (by decide)
    · simp only
  rw [hrep] at hxg
  obtain ⟨X', Y', W', hP, hY5, hinv⟩ := mcl_heisP (Or.inr rfl) hg
  refine ⟨fun _ => X', fun _ => Y', W', hP, fun _ => hY5, ?_⟩
  apply Subtype.ext
  rw [heR, Subgroup.coe_inv, hxg]
  simpa [mclTau] using hinv

theorem mclP_center_eq_bot :
    Subgroup.center ↥mclP = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : (z : Equiv.Perm (Fin 275)) ∈
      Subgroup.centralizer (mclP : Set (Equiv.Perm (Fin 275))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
  rw [mcl_centralizer_eq_bot, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem mclP_mulAut_card :
    Nat.card (MulAut ↥mclP) ≤ 2 * Nat.card ↥mclP := by
  rw [card_mclP]
  exact mcl_card_mulAut_le.trans (by norm_num)

theorem mclP_rank_le :
    ∀ B : Subgroup ↥mclP, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ 6 := by
  intro B _ hsq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [sq] using hsq x x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 ^ 7 := by
    have h1 : Nat.card B ∣ Nat.card ↥mclP := Subgroup.card_subgroup_dvd_card B
    rw [hk, card_mclP, show (898128000 : ℕ) = 2 ^ 7 * 7016625 by norm_num] at h1
    exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 7016625)).dvd_of_dvd_mul_right h1
  have hk7 : k ≤ 7 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  rw [hk]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hk6
  have hk7' : k = 7 := by omega
  have hS : Nat.card B = 2 ^ (Nat.card ↥mclP).factorization 2 := by
    rw [hk, hk7', card_mclP, show (898128000 : ℕ) = 2 ^ 7 * 7016625 by norm_num,
      factorization_two_pow_mul (by norm_num)]
  let S' : Sylow 2 ↥mclP := Sylow.ofCard B hS
  set y : ↥mclP := (mcla0 * mcla1 ^ 2) ^ 3 with hy
  have hy12 : orderOf (mcla0 * mcla1 ^ 2) = 12 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_pow]
    exact mcl_word_orders'.1
  have hy4 : orderOf y = 4 := by
    rw [hy, orderOf_pow_of_dvd (by norm_num) (by rw [hy12]; norm_num), hy12]
  have hyp : IsPGroup 2 (Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hy4]
    exact ⟨2, by norm_num⟩
  obtain ⟨T, hT⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥mclP S' T
  have hyT : y ∈ (T : Subgroup ↥mclP) := hT (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyT
  obtain ⟨b, hb, hby⟩ := hyT
  have hbB : b ∈ B := by
    rwa [show ((S' : Subgroup ↥mclP)) = B from Sylow.coe_ofCard _ _] at hb
  have hyy : y * y = 1 := by
    rw [← hby, MulAut.smul_def, MulAut.conj_apply]
    calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hsq b hbB]; group
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hyy])
  rw [hy4] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by norm_num)

theorem orderOf_two_zmod_five_mcl : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem mcl_weight_lt
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* ↥mclP) (hZ : ¬ 5 ∣ Nat.card (Subgroup.center ↥L))
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply weight_lt_of_lt_index
  have hmono : ∀ b ∈ E, (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := fun b hb =>
    Subgroup.index_antitone (QuasithinUnique.Setup.X1.fixV_anti ((Subgroup.zpowers_le).2 hb))
  by_cases hEL : E ≤ L
  ·
    have hcard : Nat.card E ≤ 2 ^ 6 := card_le_two_pow_of_le hW hirr hEL hEel e mclP_rank_le
    obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hb2 : b * b = 1 := by
      have := hEel.2 b hbE
      rwa [sq] at this
    have h8 := rank_of_heisCfg hW hirr e (ρ := 8) (p := 5) (n := 0) (by norm_num) hZ
      (by rw [orderOf_two_zmod_five_mcl]; norm_num) mcl_heisGen b (hEL hbE) hb1' hb2
    calc Nat.card E ≤ 2 ^ 6 := hcard
      _ < 2 ^ 8 := by norm_num
      _ ≤ (fixV E).index := h8.trans (hmono b hbE)
  ·
    obtain ⟨b, hbE, hbL⟩ : ∃ b ∈ E, b ∉ L := by
      by_contra h
      push Not at h
      exact hEL h
    have hb2 : b * b = 1 := by
      have := hEel.2 b hbE
      rwa [sq] at this
    have hψo : psiAut L e (hE hbE) ∉ (MulAut.conj : ↥mclP →* MulAut ↥mclP).range := by
      rintro ⟨s, hs⟩
      refine hbL (mem_of_psiAut_inner hW hq.1 hirr hE hEel e hbE s fun x => ?_)
      rw [← hs, MulAut.conj_apply]
    have hψ2 : psiAut L e (hE hbE) * psiAut L e (hE hbE) = 1 := by
      have hbb : b * b ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).mul_mem (hE hbE) (hE hbE)
      have key : ∀ (c : MulAut W) (hc : c ∈ Subgroup.normalizer (L : Set (MulAut W))), c = 1 →
          psiAut L e hc = 1 := by
        rintro c hc rfl
        exact psiAut_one e hc
      rw [← psiAut_mul e (hE hbE) (hE hbE) hbb]
      exact key _ hbb hb2
    obtain ⟨x, y, z, h, hy, hinv⟩ := mcl_outer_heis _ hψo hψ2
    have hd := two_pow_le_index_sq_of_psiAut hW e (p := 5) (n := 0) (by norm_num) hZ (hE hbE)
      hb2 h hy hinv
    rw [orderOf_two_zmod_five_mcl] at hd
    have h8 := two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) hd (ρ := 8) (by norm_num)
    have hEcard := card_le_two_mul_inf hW hq.1 hirr hE hEel e mclP_center_eq_bot mclP_mulAut_card
    have hEel' : IsElemAbelian2 (E ⊓ L) :=
      ⟨fun a ha b hb => hEel.1 a ha.1 b hb.1, fun a ha => hEel.2 a ha.1⟩
    have hE0 : Nat.card ↥(E ⊓ L) ≤ 2 ^ 6 :=
      card_le_two_pow_of_le hW hirr inf_le_right hEel' e mclP_rank_le
    calc Nat.card E ≤ 2 * 2 ^ 6 := hEcard.trans (Nat.mul_le_mul_left _ hE0)
      _ < 2 ^ 8 := by norm_num
      _ ≤ (fixV E).index := h8.trans (hmono b hbE)

noncomputable def mclCarrierEquiv :
    NativeSporadic.Carrier .McL ≃* ↥mclP :=
  mclPermEquiv

theorem mcl_center_not_dvd
    {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.Carrier .McL) :
    ¬ 5 ∣ Nat.card (Subgroup.center L) := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_McL] at h
  intro h5
  exact absurd (Nat.le_of_dvd (by decide) (h5.trans h)) (by decide)

theorem sporadicExclusion_McL :
    QuasithinUnique.Setup.X1.SporadicExclusion .McL := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  exact mcl_weight_lt hW hq hirr (e.trans mclCarrierEquiv) (mcl_center_not_dvd hq e) hE hEne hEel

theorem noIrrFFOffender_McL :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .McL).Group :=
  Proving.noIrrFFOffender_of_exclusion sporadicExclusion_McL
    CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_McL :
    GF2NoFFSporadicFor .McL :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_McL

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

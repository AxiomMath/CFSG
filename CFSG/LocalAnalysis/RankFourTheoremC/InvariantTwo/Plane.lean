module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Embeds

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.exists_isPlaneDiagonal (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D)
    (hCM : centralizer (D : Set G) ≤ M) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    ∃ g, IsPlaneDiagonal p D z g := by
  classical
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hzp : z ^ p = 1 := hDe.2 z hzD
  have hcard_z : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  obtain ⟨w₀, hw₀D, hw₀z⟩ : ∃ w₀ ∈ D, w₀ ∉ zpowers z := by
    by_contra h
    push Not at h
    have hle : D ≤ zpowers z := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    rw [hDc, hcard_z] at this
    have hp1 := hprime.one_lt
    nlinarith
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀z (h ▸ one_mem _)
  obtain ⟨x, hxN, hx⟩ := hS.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab hCM hzD hz1
    hzc hN₀M hw₀D hw₀1
  set w : G := x * z * x⁻¹ with hwdef
  have hwD : w ∈ D := (mem_normalizer_iff.mp hxN z).mp hzD
  have hline : zpowers w₀ = zpowers w := by
    rw [hx, MonoidHom.map_zpowers]
    rfl
  have hwz : w ∉ zpowers z := by
    intro hmem
    apply hw₀z
    have : w₀ ∈ zpowers w := hline ▸ mem_zpowers w₀
    exact (zpowers_le.2 hmem) this
  have hw1 : w ≠ 1 := fun h => hwz (h ▸ one_mem _)
  have hwp : w ^ p = 1 := hDe.2 w hwD
  have hzw : z * w = w * z := congrArg Subtype.val (hDe.1.is_comm.comm ⟨z, hzD⟩ ⟨w, hwD⟩)
  have hzw' : z ∉ zpowers w := by
    intro hmem
    apply hwz
    have hcard_w : Nat.card (zpowers w) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hwp hw1]
    have : zpowers z = zpowers w :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hmem) (by rw [hcard_z, hcard_w])
    exact this ▸ mem_zpowers w
  obtain ⟨n, hnP, hnN, hnC⟩ :=
    hS.exists_mem_normalizer_not_mem_centralizer hD1 hp hext hPD hDab hCM
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  have hnord : ∃ k : ℕ, n ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨b₁, hb₁, hnw⟩ := exists_transvection_exponent hDe hDc hzD hz1 hnord hnN hnz hnC hwD hwz
  set n₂ : G := x * n * x⁻¹ with hn₂def
  have hn₂N : n₂ ∈ normalizer (D : Set G) := mul_mem (mul_mem hxN hnN) (inv_mem hxN)
  have hn₂w : n₂ * w = w * n₂ := by
    calc n₂ * w = x * (n * z) * x⁻¹ := by simp only [hwdef, hn₂def]; group
      _ = x * (z * n) * x⁻¹ := by rw [hnz]
      _ = w * n₂ := by simp only [hwdef, hn₂def]; group
  have hn₂ord : ∃ k : ℕ, n₂ ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hnord
    exact ⟨k, by rw [hn₂def, conj_pow, hk]; group⟩
  have hn₂C : n₂ ∉ centralizer (D : Set G) := by
    intro h
    apply hnC
    rw [mem_centralizer_iff]
    intro d hd
    have hxd : x * d * x⁻¹ ∈ D := (mem_normalizer_iff.mp hxN d).mp hd
    have h1 := mem_centralizer_iff.mp h _ hxd
    have e : x * (d * n) * x⁻¹ = x * (n * d) * x⁻¹ := by
      calc x * (d * n) * x⁻¹ = (x * d * x⁻¹) * (x * n * x⁻¹) := by group
        _ = (x * n * x⁻¹) * (x * d * x⁻¹) := h1
        _ = x * (n * d) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨b₂, hb₂, hn₂z⟩ := exists_transvection_exponent hDe hDc hwD hw1 hn₂ord hn₂N hn₂w hn₂C
    hzD hzw'
  have hz' : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
  have hw' : n₂ * w * n₂⁻¹ = w := by rw [hn₂w, mul_inv_cancel_right]
  have hact₁ : PlaneActs p z w n !![1, ((b₁ : ℕ) : ZMod p); 0, 1] := by
    refine ⟨by simpa [zmodPow_one, zmodPow_zero] using hz', ?_⟩
    have : n * w * n⁻¹ = z ^ b₁ * w := by
      rw [hnw]; exact ((show Commute z w from hzw).pow_left b₁).eq.symm
    simpa [zmodPow_one, zmodPow_zero, zmodPow_natCast hzp] using this
  have hact₂ : PlaneActs p z w n₂ !![1, 0; ((b₂ : ℕ) : ZMod p), 1] := by
    refine ⟨?_, by simpa [zmodPow_one, zmodPow_zero] using hw'⟩
    simpa [zmodPow_one, zmodPow_zero, zmodPow_natCast hwp] using hn₂z
  obtain ⟨ν, hν0, hνord⟩ : ∃ ν : ZMod p, ν ≠ 0 ∧ orderOf ν = p - 1 := by
    obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    refine ⟨u, u.ne_zero, ?_⟩
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
      ZMod.card_units p]
  have hm1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hW₁ := PlaneActs.weyl hzp hwp hzw hb₁ hb₂ hν0 hact₁ hact₂
  have hW₂ := PlaneActs.weyl hzp hwp hzw hb₁ hb₂ hm1 hact₁ hact₂
  have hg' := hW₁.mul hzp hwp hzw hW₂
  have hM : (!![0, ν; -(ν⁻¹), 0] * !![0, -1; -((-1 : ZMod p)⁻¹), 0] :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = !![ν, 0; 0, ν⁻¹] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hν0] <;> field_simp
  rw [hM] at hg'
  obtain ⟨g', hg'N, hg'act⟩ : ∃ g' : G, g' ∈ normalizer (D : Set G) ∧
      PlaneActs p z w g' !![ν, 0; 0, ν⁻¹] :=
    ⟨_, mul_mem (mul_mem (mul_mem (pow_mem hnN _) (pow_mem hn₂N _)) (pow_mem hnN _))
      (mul_mem (mul_mem (pow_mem hnN _) (pow_mem hn₂N _)) (pow_mem hnN _)), hg'⟩
  obtain ⟨e, m, hm, hom⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g').ne' p hprime.ne_one
  have hgcop : p.Coprime (orderOf (g' ^ (p ^ e))) := by
    have hdvd : orderOf (g' ^ (p ^ e)) ∣ m :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hom]; exact pow_orderOf_eq_one g')
    exact (Nat.Prime.coprime_iff_not_dvd hprime).2 fun h => hm (h.trans hdvd)
  have hgact := hg'act.pow hzp hwp hzw (p ^ e)
  rw [diag_pow, ZMod.pow_card_pow, ZMod.pow_card_pow] at hgact
  refine ⟨g' ^ (p ^ e), pow_mem hg'N _, hgcop, ν.val, (ν⁻¹).val, ?_, ?_, ?_, ?_⟩
  · have h1 : ((ν.val * (ν⁻¹).val : ℕ) : ZMod p) = 1 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_inv_cancel₀ hν0]
    have := congrArg ZMod.val h1
    rwa [ZMod.val_natCast, ZMod.val_one] at this
  · rw [ZMod.natCast_zmod_val]
    exact hνord
  · simpa [zmodPow, zmodPow_zero] using hgact.1
  · intro d hd _
    obtain ⟨s, t, hdst⟩ := exists_pow_mul_pow_of_mem_plane hDe hDc hzD hz1 hwD hwz hd
    have hd' : d = zmodPow z (t : ZMod p) * zmodPow w (s : ZMod p) := by
      rw [hdst, zmodPow_natCast hzp, zmodPow_natCast hwp]
      exact ((show Commute w z from hzw.symm).pow_pow s t).eq
    refine ⟨((ν - ν⁻¹) * (t : ZMod p)).val, ?_⟩
    have h1 : g' ^ p ^ e * (zmodPow z (t : ZMod p) * zmodPow w (s : ZMod p)) * (g' ^ p ^ e)⁻¹ =
        zmodPow z (ν * (t : ZMod p)) * zmodPow w (ν⁻¹ * (s : ZMod p)) := by
      simpa using hgact.conj_apply hzp hwp hzw (t : ZMod p) (s : ZMod p)
    have h2 := zw_mul_zw hzp hwp hzw ((t : ZMod p) * ν⁻¹) ((s : ZMod p) * ν⁻¹)
      ((ν - ν⁻¹) * (t : ZMod p)) 0
    rw [zmodPow_zero, mul_one, exp_aux, exp_aux'] at h2
    rw [hd', h1]
    change _ = zmodPow (zmodPow z (t : ZMod p) * zmodPow w (s : ZMod p)) ν⁻¹ *
      zmodPow z ((ν - ν⁻¹) * (t : ZMod p))
    rw [zmodPow_mul_of_commute (zmodPow_comm hzw _ _), zmodPow_mul hzp, zmodPow_mul hwp]
    exact h2.symm

theorem ObstructionSetting.centralizerEmbeds_of_extremal (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D)
    (hCM : centralizer (D : Set G) ≤ M) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) (hzM : z ∈ M) :
    CentralizerEmbeds (D.subgroupOf M) ⟨z, hzM⟩ := by
  intro d hdD hdz
  have hdD' : (d : G) ∈ D := hdD
  have hd1 : (d : G) ≠ 1 := by
    intro h
    apply hdz
    have hd : d = 1 := Subtype.ext h
    rw [hd]
    exact one_mem _
  obtain ⟨x, -, hx⟩ := hS.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab hCM hzD hz1 hzc
    hN₀M hdD' hd1
  have hcz : ∀ c : centralizer ({d} : Set M),
      x⁻¹ * ((c : M) : G) * x * z = z * (x⁻¹ * ((c : M) : G) * x) := fun c =>
    conj_inv_mul_mul_comm_of_zpowers_eq hx
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2))
  have hM : ∀ c : centralizer ({d} : Set M), x⁻¹ * ((c : M) : G) * x ∈ M := fun c =>
    hN₀M (centralizer_singleton_le_normalizer_zpowers z
      (mem_centralizer_singleton_iff.mpr (hcz c)))
  have hC : ∀ c : centralizer ({d} : Set M),
      (⟨x⁻¹ * ((c : M) : G) * x, hM c⟩ : M) ∈ centralizer ({⟨z, hzM⟩} : Set M) := fun c =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext (hcz c))
  refine ⟨MonoidHom.mk' (fun c => ⟨⟨x⁻¹ * ((c : M) : G) * x, hM c⟩, hC c⟩) ?_, ?_⟩
  · intro a b
    refine Subtype.ext (Subtype.ext ?_)
    change x⁻¹ * (((a : M) : G) * ((b : M) : G)) * x =
      x⁻¹ * ((a : M) : G) * x * (x⁻¹ * ((b : M) : G) * x)
    group
  · intro a b hab
    have h : x⁻¹ * ((a : M) : G) * x = x⁻¹ * ((b : M) : G) * x :=
      congrArg (fun y : centralizer ({⟨z, hzM⟩} : Set M) => ((y : M) : G)) hab
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h)))

end CFSG.LocalAnalysis.RankFourTheoremC

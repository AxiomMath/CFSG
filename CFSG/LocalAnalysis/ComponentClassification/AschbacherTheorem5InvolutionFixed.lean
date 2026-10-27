module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionMoved

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem fixes_all_of_fixes (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {i : Fin r}
    (hti : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar i)) (k : Fin r) :
    (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar k) := by
  by_contra hk
  have hyp := hC.hyp
  obtain ⟨hr2, -, -⟩ := lemma_7_3 hin hC h k hk
  obtain ⟨j, hj⟩ := hyp.hperm t h.mem k
  have hjk : j ≠ k := fun hjk => hk (hjk ▸ hj)
  have hik : i ≠ k := fun hik => hk (hik ▸ hti)
  have hij : i = j := by
    subst hr2
    omega
  subst hij
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one t
  have hconjconj : ∀ K : Subgroup G,
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
    intro K
    rw [Subgroup.map_map]
    have hid : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      have hinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
      rw [hinv]
      calc t * (t * x * t) * t = t ^ 2 * x * t ^ 2 := by simp only [pow_two, mul_assoc]
        _ = x := by rw [ht2, one_mul, mul_one]
    rw [hid, Subgroup.map_id]
  apply hik
  apply hyp.hdistinct
  apply preimage_injective D
  rw [← hconjconj (aschbacherThm5Preimage D (Abar k)), hj, hti]

theorem conclusion_of_rankOne (hyp : Hyp61 G D r Abar) (hr2 : r = 2)
    {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c)
    (hcall : ∀ k l, c k = c l)
    (hrank : ∀ k, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) ≤ 1) :
    Conclusion G D r Abar := by
  subst hr2
  refine Or.inr ⟨rfl, fun i' j' hij' => ⟨canonical_two_factor_product D Abar hyp.hcomm
    hyp.hgen i' j' hij', le_antisymm (hrank i') (one_le_pRank_factor hyp i'), ?_⟩⟩
  intro a₁ ha₁ a₂ ha₂ ha₁2 ha₂2 hcomm12 _ _
  left
  have ha₁D : a₁ ∈ D := preimage_le D _ ha₁
  have ha₂D : a₂ ∈ D := preimage_le D _ ha₂
  have hq₁ : QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨a₁, ha₁D⟩ = c i' :=
    hc.unique i' _ ((mem_preimage_iff D _ ⟨a₁, ha₁D⟩).mp ha₁) (orderOf_mk_eq_two ha₁2)
  have hq₂ : QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨a₂, ha₂D⟩ = c i' := by
    rw [hcall i' j']
    exact hc.unique j' _ ((mem_preimage_iff D _ ⟨a₂, ha₂D⟩).mp ha₂) (orderOf_mk_eq_two ha₂2)
  have hmem : (⟨a₁, ha₁D⟩ : D)⁻¹ * ⟨a₂, ha₂D⟩ ∈ aschbacherThm5OddCore D := by
    rw [← QuotientGroup.eq]
    exact hq₁.trans hq₂.symm
  set x : D := (⟨a₁, ha₁D⟩ : D)⁻¹ * ⟨a₂, ha₂D⟩ with hx
  have hinv₁ : a₁⁻¹ = a₁ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← ha₁2, pow_orderOf_eq_one]
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    change (a₁⁻¹ * a₂) ^ 2 = 1
    rw [hinv₁, pow_two, mul_assoc, ← mul_assoc a₂, ← hcomm12, mul_assoc, ← pow_two a₂,
      ← ha₂2, pow_orderOf_eq_one, mul_one, ← pow_two, ← ha₁2, pow_orderOf_eq_one]
  have hx1 : x = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hx2
    have hodd := Subgroup.orderOf_dvd_natCard (aschbacherThm5OddCore D) hmem
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · rw [h2] at hodd
      exact absurd (even_iff_two_dvd.mpr hodd) (Nat.not_even_iff_odd.mpr (oddCore_odd D))
  have := congrArg Subtype.val hx1
  change a₁⁻¹ * a₂ = 1 at this
  rw [inv_mul_eq_one] at this
  exact this

theorem exists_rankOneFactors (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {i : Fin r} (hri : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1) :
    ∃ c : Fin r → D ⧸ aschbacherThm5OddCore D, RankOneFactors Abar c := by
  have hri' : CFSG.Open.pRank 2 (Abar i) ≤ 1 := (pRank_le_preimage _).trans hri
  obtain ⟨c₀, hc₀, hc₀2, huniq, -⟩ := unique_involution_of_rank_one_image
    (hC.hyp.hsemisimple i) (MonoidHom.id (Abar i)) Function.surjective_id (by
      rw [MonoidHom.ker_id]
      exact bot_le) ((pRank_type_le _).trans hri')
  obtain ⟨c, hc, -⟩ := rankOneFactors_of_one hin hC hc₀ hc₀2 huniq
  exact ⟨c, hc⟩

theorem rankOne_fixed_impossible (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g)
    (hfix : ∀ k, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar k))
    {i : Fin r} (hri : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1) : False := by
  have hyp := hC.hyp
  obtain ⟨c, hc⟩ := exists_rankOneFactors hin hC hri
  set σ := onQuotient D ⟨t, h.mem⟩
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one t
  have hσ : ∀ q, σ (σ q) = q := onQuotient_involutive ht2
  have hσc : ∀ k, σ (c k) = c k := fun k => onQuotient_c hc ⟨t, h.mem⟩ (hfix k)
  have hcall : ∀ k l, c k = c l := by
    intro k l
    by_contra hkl
    exact no_commuting_pair hin hC h (hc.orderOf_eq k) (hc.orderOf_eq l)
      (commute_of_mem_centralizer_all hyp (fun m => c_mem_centralizer hyp hc k m) (c l)) hkl
      (hσc k) (hσc l) k (c_mem_centralizer hyp hc k k) (c_mem_centralizer hyp hc l k)
  have hrank : ∀ k, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) ≤ 1 := by
    intro k
    obtain ⟨x, -, hxk⟩ := hin.lemma_6_3 hC i k
    rw [← hxk, pRank_map_conj]
    exact hri
  by_cases hr2 : r = 2
  · exact hC.fails (conclusion_of_rankOne hyp hr2 hc hcall hrank)
  have h3 : 3 ≤ r := by have := two_le hC; omega
  set k₀ : Fin r := ⟨0, by omega⟩
  set k₁ : Fin r := ⟨1, by omega⟩
  set k₂ : Fin r := ⟨2, by omega⟩
  have h01 : k₀ ≠ k₁ := by simp [k₀, k₁, Fin.ext_iff]
  have h02 : k₀ ≠ k₂ := by simp [k₀, k₂, Fin.ext_iff]
  have h12 : k₁ ≠ k₂ := by simp [k₁, k₂, Fin.ext_iff]
  have hy : ∀ k, ∃ y ∈ Abar k, orderOf y = 4 ∧ (σ y = y ∨ σ y = y⁻¹) := fun k =>
    exists_orderOf_four_fixed_or_inverted_mem (semisimple_perfect _ (hyp.hsemisimple k))
      (semisimple_ne_bot _ (hyp.hsemisimple k)) (hc.mem k) (hc.orderOf_eq k) (hc.unique k) σ hσ
      (map_onQuotient_factor ⟨t, h.mem⟩ (hfix k))
  have hpair : ∀ k l m : Fin r, k ≠ l → m ≠ k → m ≠ l → ∀ yk ∈ Abar k, ∀ yl ∈ Abar l,
      orderOf yk = 4 → orderOf yl = 4 → σ (yk * yl) = yk * yl → False := by
    intro k l m hkl hmk hml yk hyk yl hyl hyk4 hyl4 hσu
    have hcomm : yk * yl = yl * yk := hyp.hcomm k l hkl yk hyk yl hyl
    have hu2 : (yk * yl) * (yk * yl) = 1 := by
      rw [← pow_two, (show Commute yk yl from hcomm).mul_pow, sq_eq_c hc hyk hyk4,
        sq_eq_c hc hyl hyl4, hcall l k, ← pow_two, ← hc.orderOf_eq k, pow_orderOf_eq_one]
    have hyln : yl ∉ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) :=
      not_mem_centralizer_factor hyp hc hyl hyl4
    have hu1 : yk * yl ≠ 1 := by
      intro h1
      apply hyln
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (mem_centralizer_factor hyp (Ne.symm hkl) hyk)
    have huc : yk * yl ≠ c k := by
      intro h1
      apply hyln
      have : yl = yk⁻¹ * c k := by rw [← h1]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_centralizer_factor hyp (Ne.symm hkl) hyk))
        (c_mem_centralizer hyp hc k l)
    exact no_commuting_pair hin hC h (hc.orderOf_eq k)
      (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1)
      (commute_of_mem_centralizer_all hyp (fun n => c_mem_centralizer hyp hc k n) _)
      (Ne.symm huc) (hσc k) hσu m (c_mem_centralizer hyp hc k m)
      (Subgroup.mul_mem _ (mem_centralizer_factor hyp hmk hyk) (mem_centralizer_factor hyp hml hyl))
  obtain ⟨y₀, hy₀, hy₀4, hσy₀⟩ := hy k₀
  obtain ⟨y₁, hy₁, hy₁4, hσy₁⟩ := hy k₁
  obtain ⟨y₂, hy₂, hy₂4, hσy₂⟩ := hy k₂
  have hfixed : ∀ {k l : Fin r} {yk yl : D ⧸ aschbacherThm5OddCore D}, k ≠ l → yk ∈ Abar k →
      yl ∈ Abar l → orderOf yk = 4 → orderOf yl = 4 → σ yk = yk → σ yl = yl →
      σ (yk * yl) = yk * yl := fun _ _ _ _ _ hk hl => by rw [map_mul, hk, hl]
  have hinverted : ∀ {k l : Fin r} {yk yl : D ⧸ aschbacherThm5OddCore D}, k ≠ l → yk ∈ Abar k →
      yl ∈ Abar l → orderOf yk = 4 → orderOf yl = 4 → σ yk = yk⁻¹ → σ yl = yl⁻¹ →
      σ (yk * yl) = yk * yl := by
    intro k l yk yl hkl hyk hyl hyk4 hyl4 hk hl
    have hcomm : yk * yl = yl * yk := hyp.hcomm k l hkl yk hyk yl hyl
    have hu2 : (yk * yl) * (yk * yl) = 1 := by
      rw [← pow_two, (show Commute yk yl from hcomm).mul_pow, sq_eq_c hc hyk hyk4,
        sq_eq_c hc hyl hyl4, hcall l k, ← pow_two, ← hc.orderOf_eq k, pow_orderOf_eq_one]
    rw [map_mul, hk, hl, ← mul_inv_rev, ← hcomm, inv_eq_of_mul_eq_one_left hu2]
  rcases hσy₀ with h0 | h0 <;> rcases hσy₁ with h1 | h1
  · exact hpair k₀ k₁ k₂ h01 h02.symm h12.symm y₀ hy₀ y₁ hy₁ hy₀4 hy₁4
      (hfixed h01 hy₀ hy₁ hy₀4 hy₁4 h0 h1)
  · rcases hσy₂ with h2 | h2
    · exact hpair k₀ k₂ k₁ h02 h01.symm h12 y₀ hy₀ y₂ hy₂ hy₀4 hy₂4
        (hfixed h02 hy₀ hy₂ hy₀4 hy₂4 h0 h2)
    · exact hpair k₁ k₂ k₀ h12 h01 h02 y₁ hy₁ y₂ hy₂ hy₁4 hy₂4
        (hinverted h12 hy₁ hy₂ hy₁4 hy₂4 h1 h2)
  · rcases hσy₂ with h2 | h2
    · exact hpair k₁ k₂ k₀ h12 h01 h02 y₁ hy₁ y₂ hy₂ hy₁4 hy₂4
        (hfixed h12 hy₁ hy₂ hy₁4 hy₂4 h1 h2)
    · exact hpair k₀ k₂ k₁ h02 h01.symm h12 y₀ hy₀ y₂ hy₂ hy₀4 hy₂4
        (hinverted h02 hy₀ hy₂ hy₀4 hy₂4 h0 h2)
  · exact hpair k₀ k₁ k₂ h01 h02.symm h12.symm y₀ hy₀ y₁ hy₁ hy₀4 hy₁4
      (hinverted h01 hy₀ hy₁ hy₀4 hy₁4 h0 h1)

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionOrderFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionDiagonal

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem sq_eq_c {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c)
    {k : Fin r} {x : D ⧸ aschbacherThm5OddCore D} (hx : x ∈ Abar k) (hx4 : orderOf x = 4) :
    x ^ 2 = c k := by
  apply hc.unique k _ ((Abar k).pow_mem hx 2)
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hx4]; norm_num), hx4]

theorem not_mem_centralizer_factor (hyp : Hyp61 G D r Abar)
    {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c) {k : Fin r}
    {x : D ⧸ aschbacherThm5OddCore D} (hx : x ∈ Abar k) (hx4 : orderOf x = 4) :
    x ∉ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D)) :=
  not_mem_centralizer_of_orderOf_four (semisimple_perfect _ (hyp.hsemisimple k))
    (semisimple_ne_bot _ (hyp.hsemisimple k)) (hc.unique k) hx hx4

theorem exists_orderOf_four_factor (hyp : Hyp61 G D r Abar)
    {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c) (k : Fin r) :
    ∃ x ∈ Abar k, orderOf x = 4 :=
  exists_orderOf_four_mem (semisimple_perfect _ (hyp.hsemisimple k))
    (semisimple_ne_bot _ (hyp.hsemisimple k)) (hc.unique k)

theorem commute_of_mem_centralizer_all (hyp : Hyp61 G D r Abar)
    {e : D ⧸ aschbacherThm5OddCore D}
    (he : ∀ l, e ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)))
    (u : D ⧸ aschbacherThm5OddCore D) : e * u = u * e := by
  have hle : (⊤ : Subgroup (D ⧸ aschbacherThm5OddCore D)) ≤
      Subgroup.centralizer ({e} : Set (D ⧸ aschbacherThm5OddCore D)) := by
    rw [← hyp.hgen]
    refine iSup_le fun l x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (he l) x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top u))).symm

theorem step_two (hin : SectionSevenBase) (hC : Counterexample G D r Abar) {t g : G}
    (h : Hyp71 D t g) {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c)
    {i j : Fin r} (hij : i ≠ j)
    (htij : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar j))
    (hcij : c i ≠ c j) : False := by
  have hyp := hC.hyp
  set σ := onQuotient D ⟨t, h.mem⟩
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one t
  have hσ : ∀ q, σ (σ q) = q := onQuotient_involutive ht2
  have hmapij : (Abar i).map σ.toMonoidHom = Abar j := map_onQuotient_factor ⟨t, h.mem⟩ htij
  have hσi : σ (c i) = c j := onQuotient_c hc ⟨t, h.mem⟩ htij
  have hσj : σ (c j) = c i := by rw [← hσi, hσ]
  have hσmem : ∀ x ∈ Abar i, σ x ∈ Abar j := fun x hx =>
    hmapij ▸ Subgroup.mem_map_of_mem _ hx
  set cc := c i * c j with hccdef
  have hcomm_ij : c i * c j = c j * c i := hyp.hcomm i j hij _ (hc.mem i) _ (hc.mem j)
  have hci2 : c i * c i = 1 := by rw [← pow_two, ← hc.orderOf_eq i, pow_orderOf_eq_one]
  have hcj2 : c j * c j = 1 := by rw [← pow_two, ← hc.orderOf_eq j, pow_orderOf_eq_one]
  have hccsq : cc * cc = 1 := by
    rw [hccdef, mul_assoc, ← mul_assoc (c j), ← hcomm_ij, mul_assoc, hcj2, mul_one, hci2]
  have hcc1 : cc ≠ 1 := by
    intro h1
    apply hcij
    rw [hccdef] at h1
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left hcj2]
  have hcc2 : orderOf cc = 2 := orderOf_eq_prime (by rw [pow_two]; exact hccsq) hcc1
  have hσcc : σ cc = cc := by rw [hccdef, map_mul, hσi, hσj, hcomm_ij]
  have hccent : ∀ l, cc ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) :=
    fun l => Subgroup.mul_mem _ (c_mem_centralizer hyp hc i l) (c_mem_centralizer hyp hc j l)
  have hcontra : ∀ u : D ⧸ aschbacherThm5OddCore D, u * u = 1 → σ u = u → u ≠ 1 → u ≠ cc →
      ∀ m, u ∈ Subgroup.centralizer (Abar m : Set (D ⧸ aschbacherThm5OddCore D)) → False := by
    intro u hu2 hσu hu1 hucc m hum
    exact no_commuting_pair hin hC h hcc2 (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1)
      (commute_of_mem_centralizer_all hyp hccent u) (Ne.symm hucc) hσcc hσu m (hccent m) hum
  have hcentral_eq : ∀ e : D ⧸ aschbacherThm5OddCore D, e * e = 1 → e ≠ 1 → σ e = e →
      (∀ l, e ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D))) → e = cc := by
    intro e he2 he1 hσe hel
    by_contra hne
    exact hcontra e he2 hσe he1 hne i (hel i)
  have hcommi : ∀ x ∈ Abar i, ∀ y ∈ Abar i, σ x * y = y * σ x := fun x hx y hy =>
    hyp.hcomm j i (Ne.symm hij) (σ x) (hσmem x hx) y hy
  by_cases hr4 : r ≤ 4
  ·
    set δ := diagonal σ (Abar i) hcommi
    have : Group.IsPerfect (Abar i) := semisimple_perfect _ (hyp.hsemisimple i)
    have hΔperf : Group.IsPerfect δ.range := Group.IsPerfect.ofSurjective δ.rangeRestrict_surjective
    have hfix : ∀ q ∈ δ.range, σ q = q := by
      rintro _ ⟨x, rfl⟩
      exact diagonal_fixed hσ x
    have hccΔ : cc ∈ δ.range := ⟨⟨c i, hc.mem i⟩, by rw [diagonal_apply]; exact congrArg _ hσi⟩
    obtain ⟨B, hBC, hBperf, z, hzB, hz2, hzD, hzc⟩ :=
      exists_perfect_lift h.mem h.orderOf_eq hΔperf hfix hccΔ hcc2
    set H := Subgroup.normalizer (D : Set G)
    have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; omega
    have hzcent : aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (Abar i)) z :=
      (centralizes_iff_mem_centralizer_quotient (Abar i) ⟨z, hzD⟩).mpr (by
        rw [hzc]
        exact hccent i)
    have hCz : Subgroup.centralizer ({z} : Set G) ≤ H :=
      centralizer_le_of_centralizes hC i (two_power_of_orderOf hz2) hz1 hzcent
    have hzHg : z ∈ rightConjugate H g := h.centralizer_le (hBC hzB)
    have hgH : g ∉ H := h.not_mem hyp
    have hg'H : g⁻¹ ∉ H := fun hmem => hgH (by simpa using H.inv_mem hmem)
    set w := g * z * g⁻¹ with hwdef
    have hwH : w ∈ H := (mem_rightConjugate_iff H g z).mp hzHg
    have hw : Hyp71 D w g⁻¹ :=
      { mem := hwH
        orderOf_eq := by
          rw [hwdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact hz2
        centralizer_le := by
          intro x hx
          rw [mem_rightConjugate_iff, inv_inv]
          apply hCz
          rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
          calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
            _ = z * (g⁻¹ * x * g) := by group
        ne := fun heq => hg'H ((rightConjugate_normalizer_eq_iff hyp g⁻¹).mp heq) }
    set B' := B.map (MulAut.conj g).toMonoidHom
    have hB'H : B' ≤ H := by
      rintro _ ⟨b, hb, rfl⟩
      exact (mem_rightConjugate_iff H g b).mp (h.centralizer_le (hBC hb))
    have hB'perf : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
      (f := (B.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom)
      (MulEquiv.surjective _)
    have hwB' : w ∈ B' := ⟨z, hzB, rfl⟩
    have hfixw : ∀ l, (aschbacherThm5Preimage D (Abar l)).map (MulAut.conj w).toMonoidHom =
        aschbacherThm5Preimage D (Abar l) := fun l =>
      perfect_fixes_factors hyp hr4 hB'H hB'perf hwB' l
    exact no_commuting_pair hin hC hw (hc.orderOf_eq i) (hc.orderOf_eq j) hcomm_ij hcij
      (onQuotient_c hc ⟨w, hwH⟩ (hfixw i)) (onQuotient_c hc ⟨w, hwH⟩ (hfixw j)) i
      (c_mem_centralizer hyp hc i i) (c_mem_centralizer hyp hc j i)
  ·
    push Not at hr4
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin r, k ≠ i ∧ k ≠ j := by
      by_contra hno
      push Not at hno
      have hsub : (Finset.univ : Finset (Fin r)) ⊆ {i, j} := fun l _ => by
        by_cases hli : l = i
        · simp [hli]
        · simp [hno l hli]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have := this.trans (Finset.card_insert_le _ _)
      simp at this
      omega
    obtain ⟨k', hk'⟩ := hyp.hperm t h.mem k
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
    have hji : (aschbacherThm5Preimage D (Abar j)).map (MulAut.conj t).toMonoidHom =
        aschbacherThm5Preimage D (Abar i) := by rw [← htij, hconjconj]
    have hpre_inj : ∀ {l l' : Fin r}, aschbacherThm5Preimage D (Abar l) =
        aschbacherThm5Preimage D (Abar l') → l = l' := fun heq =>
      hyp.hdistinct (preimage_injective D heq)
    have hmap_inj : ∀ {K K' : Subgroup G}, K.map (MulAut.conj t).toMonoidHom =
        K'.map (MulAut.conj t).toMonoidHom → K = K' := fun heq =>
      Subgroup.map_injective (MulAut.conj t).injective heq
    have hk'i : k' ≠ i := by
      rintro rfl
      exact hkj (hpre_inj (hmap_inj (hk'.trans hji.symm)))
    have hk'j : k' ≠ j := by
      rintro rfl
      exact hki (hpre_inj (hmap_inj (hk'.trans htij.symm)))
    obtain ⟨m, hmi, hmj, hmk, hmk'⟩ : ∃ m : Fin r, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ k' := by
      by_contra hno
      push Not at hno
      have hsub : (Finset.univ : Finset (Fin r)) ⊆ {i, j, k, k'} := fun l _ => by
        by_cases hli : l = i
        · simp [hli]
        by_cases hlj : l = j
        · simp [hlj]
        by_cases hlk : l = k
        · simp [hlk]
        simp [hno l hli hlj hlk]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h4 : ({i, j, k, k'} : Finset (Fin r)).card ≤ 4 :=
        (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
      omega
    obtain ⟨x, hxi, hx4⟩ := exists_orderOf_four_factor hyp hc i
    have hx2 : x ^ 2 = c i := sq_eq_c hc hxi hx4
    have hσx2 : (σ x) ^ 2 = c j := by rw [← map_pow, hx2, hσi]
    have hσxj : σ x ∈ Abar j := hσmem x hxi
    have hxσ : Commute x (σ x) := (hcommi x hxi x hxi).symm
    have hcj1 : (c j)⁻¹ = c j := inv_eq_of_mul_eq_one_left hcj2
    set vp := x * σ x with hvp
    set vm := x * (σ x)⁻¹ with hvm
    have hvp2 : vp * vp = cc := by
      rw [← pow_two, hvp, hxσ.mul_pow, hx2, hσx2]
    have hvm2 : vm * vm = cc := by
      rw [← pow_two, hvm, hxσ.inv_right.mul_pow, inv_pow, hx2, hσx2, hcj1]
    have hσvp : σ vp = vp := by rw [hvp, map_mul, hσ, hxσ.eq]
    have hσvm : σ vm = vm⁻¹ := by
      rw [hvm, map_mul, map_inv, hσ, mul_inv_rev, inv_inv]
    have hvcent : ∀ l, l ≠ i → l ≠ j →
        vp ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) ∧
        vm ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) := by
      intro l hli hlj
      have h1 := mem_centralizer_factor hyp hli hxi
      have h2 := mem_centralizer_factor hyp hlj hσxj
      exact ⟨Subgroup.mul_mem _ h1 h2, Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)⟩
    have hfinish : ∀ (n : Fin r) (v y : D ⧸ aschbacherThm5OddCore D), v * v = cc → y * y = cc →
        v * y = y * v → σ (v * y) = v * y →
        v ∈ Subgroup.centralizer (Abar n : Set (D ⧸ aschbacherThm5OddCore D)) →
        y ∉ Subgroup.centralizer (Abar n : Set (D ⧸ aschbacherThm5OddCore D)) →
        ∀ l, v ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) →
          y ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) → False := by
      intro n v y hv2 hy2 hvy hσu hvn hyn l hvl hyl
      have hc' : Commute v y := hvy
      have hu2 : (v * y) * (v * y) = 1 := by
        rw [← pow_two, hc'.mul_pow, pow_two, pow_two, hv2, hy2, hccsq]
      have hu1 : v * y ≠ 1 := by
        intro h1
        apply hyn
        rw [eq_inv_of_mul_eq_one_right h1]
        exact Subgroup.inv_mem _ hvn
      have hucc : v * y ≠ cc := by
        intro h1
        apply hyn
        have hyv : y = v⁻¹ * cc := by rw [← h1]; group
        rw [hyv]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hvn) (hccent n)
      exact hcontra (v * y) hu2 hσu hu1 hucc l (Subgroup.mul_mem _ hvl hyl)
    have hcomm_of : ∀ {n : Fin r} {v y : D ⧸ aschbacherThm5OddCore D},
        v ∈ Subgroup.centralizer (Abar n : Set (D ⧸ aschbacherThm5OddCore D)) → y ∈ Abar n →
        v * y = y * v := fun hv hy => (Subgroup.mem_centralizer_iff.mp hv _ hy).symm
    by_cases hkk : k' = k
    ·
      have hk'' : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
          aschbacherThm5Preimage D (Abar k) := hkk ▸ hk'
      have hmapk : (Abar k).map σ.toMonoidHom = Abar k := map_onQuotient_factor ⟨t, h.mem⟩ hk''
      have hσck : σ (c k) = c k := onQuotient_c hc ⟨t, h.mem⟩ hk''
      have hck2 : c k * c k = 1 := by rw [← pow_two, ← hc.orderOf_eq k, pow_orderOf_eq_one]
      have hck1 : c k ≠ 1 := fun h1 => by
        have := hc.orderOf_eq k
        rw [h1, orderOf_one] at this
        omega
      have hck : c k = cc := hcentral_eq (c k) hck2 hck1 hσck (c_mem_centralizer hyp hc k)
      obtain ⟨y, hyk, hy4, hy⟩ := exists_orderOf_four_fixed_or_inverted_mem
        (semisimple_perfect _ (hyp.hsemisimple k)) (semisimple_ne_bot _ (hyp.hsemisimple k))
        (hc.mem k) (hc.orderOf_eq k) (hc.unique k) σ hσ hmapk
      have hy2 : y * y = cc := by rw [← pow_two, sq_eq_c hc hyk hy4, hck]
      have hyn := not_mem_centralizer_factor hyp hc hyk hy4
      have hym := mem_centralizer_factor hyp hmk hyk
      rcases hy with hy | hy
      · exact hfinish k vp y hvp2 hy2 (hcomm_of (hvcent k hki hkj).1 hyk)
          (by rw [map_mul, hσvp, hy]) (hvcent k hki hkj).1 hyn m (hvcent m hmi hmj).1 hym
      · have hvy := hcomm_of (hvcent k hki hkj).2 hyk
        have hu2 : (vm * y) * (vm * y) = 1 := by
          rw [← pow_two, (show Commute vm y from hvy).mul_pow, pow_two, pow_two, hvm2, hy2,
            hccsq]
        have hσu : σ (vm * y) = vm * y := by
          rw [map_mul, hσvm, hy, ← mul_inv_rev, ← hvy, inv_eq_of_mul_eq_one_left hu2]
        exact hfinish k vm y hvm2 hy2 hvy hσu (hvcent k hki hkj).2 hyn m (hvcent m hmi hmj).2
          hym
    ·
      have hmapk : (Abar k).map σ.toMonoidHom = Abar k' := map_onQuotient_factor ⟨t, h.mem⟩ hk'
      have hσk : ∀ y ∈ Abar k, σ y ∈ Abar k' := fun y hy => hmapk ▸ Subgroup.mem_map_of_mem _ hy
      have hσck : σ (c k) = c k' := onQuotient_c hc ⟨t, h.mem⟩ hk'
      have hσck' : σ (c k') = c k := by rw [← hσck, hσ]
      obtain ⟨xk, hxk, hxk4⟩ := exists_orderOf_four_factor hyp hc k
      have hxk2 : xk ^ 2 = c k := sq_eq_c hc hxk hxk4
      have hσxk2 : (σ xk) ^ 2 = c k' := by rw [← map_pow, hxk2, hσck]
      have hσxkk' : σ xk ∈ Abar k' := hσk xk hxk
      have hxkσ : Commute xk (σ xk) := hyp.hcomm k k' (Ne.symm hkk) xk hxk (σ xk) hσxkk'
      set wp := xk * σ xk with hwp
      have hσwp : σ wp = wp := by rw [hwp, map_mul, hσ, hxkσ.eq]
      have hwp2 : wp * wp = c k * c k' := by rw [← pow_two, hwp, hxkσ.mul_pow, hxk2, hσxk2]
      have hwpn : wp ∉ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D)) := by
        intro hwk
        apply not_mem_centralizer_factor hyp hc hxk hxk4
        have hxkw : xk = wp * (σ xk)⁻¹ := by rw [hwp]; group
        rw [hxkw]
        exact Subgroup.mul_mem _ hwk
          (Subgroup.inv_mem _ (mem_centralizer_factor hyp (Ne.symm hkk) hσxkk'))
      have hwpm : wp ∈ Subgroup.centralizer (Abar m : Set (D ⧸ aschbacherThm5OddCore D)) :=
        Subgroup.mul_mem _ (mem_centralizer_factor hyp hmk hxk)
          (mem_centralizer_factor hyp hmk' hσxkk')
      have hcomm_kk' : c k * c k' = c k' * c k :=
        hyp.hcomm k k' (Ne.symm hkk) _ (hc.mem k) _ (hc.mem k')
      have hck2 : c k * c k = 1 := by rw [← pow_two, ← hc.orderOf_eq k, pow_orderOf_eq_one]
      have hck'2 : c k' * c k' = 1 := by
        rw [← pow_two, ← hc.orderOf_eq k', pow_orderOf_eq_one]
      by_cases hckk : c k = c k'
      ·
        have hwp1 : wp * wp = 1 := by rw [hwp2, ← hckk, hck2]
        exact hcontra wp hwp1 hσwp (fun h1 => hwpn (h1 ▸ Subgroup.one_mem _))
          (fun h1 => hwpn (h1 ▸ hccent k)) m hwpm
      ·
        have he2 : (c k * c k') * (c k * c k') = 1 := by
          rw [mul_assoc, ← mul_assoc (c k'), ← hcomm_kk', mul_assoc, hck'2, mul_one, hck2]
        have he1 : c k * c k' ≠ 1 := by
          intro h1
          apply hckk
          rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left hck'2]
        have hσe : σ (c k * c k') = c k * c k' := by rw [map_mul, hσck, hσck', hcomm_kk']
        have he : c k * c k' = cc := hcentral_eq _ he2 he1 hσe fun l =>
          Subgroup.mul_mem _ (c_mem_centralizer hyp hc k l) (c_mem_centralizer hyp hc k' l)
        have hvpk := (hvcent k hki hkj).1
        have hvpk' := (hvcent k' hk'i hk'j).1
        have hvw : vp * wp = wp * vp := by
          rw [hwp, ← mul_assoc, hcomm_of hvpk hxk, mul_assoc, hcomm_of hvpk' hσxkk', mul_assoc]
        exact hfinish k vp wp hvp2 (hwp2.trans he) hvw (by rw [map_mul, hσvp, hσwp]) hvpk hwpn
          m (hvcent m hmi hmj).1 hwpm

section Ranks

variable {K : Type*} [Group K] [Finite K]

theorem exists_elemAbelian_lift (N : Subgroup K) [N.Normal] (hN : Odd (Nat.card N))
    {C : Subgroup K} {V : Subgroup (K ⧸ N)} (hV : IsElemAbelian 2 V) (hV2 : IsPGroup 2 V)
    (hVC : V ≤ C.map (QuotientGroup.mk' N)) :
    ∃ W : Subgroup K, W ≤ C ∧ IsElemAbelian 2 W ∧ Nat.card W = Nat.card V := by
  obtain ⟨W, hWC, hW2, hWcard, hWV⟩ := exists_isPGroup_lift N hN hV2 hVC
  have hinj := fun {u v : K} (hu : u ∈ W) (hv : v ∈ W) =>
    AschbacherToolkit.quotient_injective_on_of_isPGroup N hN hW2 hu hv
  have hVc := hV.1
  refine ⟨W, hWC, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hWcard⟩
  · apply hinj (W.mul_mem a.2 b.2) (W.mul_mem b.2 a.2)
    have ha : QuotientGroup.mk' N (a : K) ∈ V := hWV ▸ Subgroup.mem_map_of_mem _ a.2
    have hb : QuotientGroup.mk' N (b : K) ∈ V := hWV ▸ Subgroup.mem_map_of_mem _ b.2
    have := congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : V) ⟨_, hb⟩)
    simpa only [map_mul, Subgroup.coe_mul] using this
  · apply hinj (W.pow_mem hx 2) W.one_mem
    have hxV : QuotientGroup.mk' N x ∈ V := hWV ▸ Subgroup.mem_map_of_mem _ hx
    rw [map_pow, hV.2 _ hxV, map_one]

end Ranks

theorem pRank_le_preimage (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    CFSG.Open.pRank 2 Ā ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D Ā) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEĀ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two Ā
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  have hEC : E ≤ (Ā.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))).map
      (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    exact hEĀ
  obtain ⟨W, hWC, hW, hWcard⟩ := exists_elemAbelian_lift (aschbacherThm5OddCore D)
    (oddCore_odd D) hE hE2 hEC
  refine CFSG.SectionRank.le_pRank one_lt_two (E := W.map D.subtype) (Subgroup.map_mono hWC)
    (CFSG.SectionRank.isElemAbelian_map hW _) ?_
  rw [Subgroup.card_map_of_injective D.subtype_injective, hWcard, hcard]

theorem pRank_map_conj (K : Subgroup G) (x : G) :
    CFSG.Open.pRank 2 (K.map (MulAut.conj x).toMonoidHom) = CFSG.Open.pRank 2 K := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two (MulAut.conj x⁻¹).toMonoidHom
      (MulAut.conj x⁻¹).injective (K.map (MulAut.conj x).toMonoidHom)
    have hK : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = K := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id K
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    rwa [hK] at h
  · exact CFSG.SectionRank.pRank_le_map one_lt_two _ (MulAut.conj x).injective K

theorem one_le_pRank_factor (hyp : Hyp61 G D r Abar) (k : Fin r) :
    1 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (aschbacherThm5Preimage D (Abar k)) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := aschbacherThm5Preimage D (Abar k)) 2
    (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp (factor_even hyp k))
  have ha2 : orderOf (a : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
  refine CFSG.SectionRank.le_pRank one_lt_two (E := Subgroup.zpowers (a : G))
    (Subgroup.zpowers_le.mpr a.2) ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩ ?_
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change (x : G) * y = y * x
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← ha2, pow_orderOf_eq_one, one_zpow]
  · rw [Nat.card_zpowers, ha2, pow_one]

theorem orderOf_mk_eq_two {d : D} (hd : orderOf (d : G) = 2) :
    orderOf (QuotientGroup.mk' (aschbacherThm5OddCore D) d) = 2 := by
  have hd' : orderOf d = 2 := by rw [← Subgroup.orderOf_coe]; exact hd
  apply orderOf_eq_prime
  · rw [← map_pow, ← hd', pow_orderOf_eq_one, map_one]
  · intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard (aschbacherThm5OddCore D) h1
    rw [hd'] at hdvd
    exact (Nat.not_even_iff_odd.mpr (oddCore_odd D)) (even_iff_two_dvd.mpr hdvd)

theorem lemma_7_3 (hin : SectionSevenBase) (hC : Counterexample G D r Abar) {t g : G}
    (h : Hyp71 D t g) (i : Fin r)
    (hmove : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj t).toMonoidHom ≠
      aschbacherThm5Preimage D (Abar i)) :
    r = 2 ∧ (∀ d ∈ D, ∃ a ∈ aschbacherThm5Preimage D (Abar i),
        ∃ b ∈ (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj t).toMonoidHom, d = a * b) ∧
      2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) := by
  have hyp := hC.hyp
  obtain ⟨j, hj⟩ := hyp.hperm t h.mem i
  have hij : i ≠ j := by
    rintro rfl
    exact hmove hj
  set σ := onQuotient D ⟨t, h.mem⟩
  have hr2 : r = 2 := by
    by_contra hr
    have h2 := two_le hC
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin r, k ≠ i ∧ k ≠ j := by
      by_contra hno
      push Not at hno
      have hsub : (Finset.univ : Finset (Fin r)) ⊆ {i, j} := fun l _ => by
        by_cases hli : l = i
        · simp [hli]
        · simp [hno l hli]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have := this.trans (Finset.card_insert_le _ _)
      simp at this
      omega
    obtain ⟨c₀, hc₀, hc₀2, huniq, hσc₀⟩ := unique_involution_of_moved hin hC h hij hki hkj hj
    obtain ⟨c, hc, hci⟩ := rankOneFactors_of_one hin hC hc₀ hc₀2 huniq
    have hcj : σ (c i) = c j := onQuotient_c hc ⟨t, h.mem⟩ hj
    exact step_two hin hC h hc hij hj (by rw [← hcj, hci]; exact fun he => hσc₀ he.symm)
  refine ⟨hr2, ?_, ?_⟩
  · subst hr2
    rw [hj]
    exact canonical_two_factor_product D Abar hyp.hcomm hyp.hgen i j hij
  · by_contra hlt
    push Not at hlt
    have hri : CFSG.Open.pRank 2 (Abar i) ≤ 1 := (pRank_le_preimage _).trans (by omega)
    obtain ⟨c₀, hc₀, hc₀2, huniq, -⟩ := unique_involution_of_rank_one_image (hyp.hsemisimple i)
      (MonoidHom.id (Abar i)) Function.surjective_id (by
        rw [MonoidHom.ker_id]
        exact bot_le) ((pRank_type_le _).trans hri)
    obtain ⟨c, hc, hci⟩ := rankOneFactors_of_one hin hC hc₀ hc₀2 huniq
    by_cases hcij : c i = c j
    ·
      apply hC.fails
      subst hr2
      have hrank : ∀ k : Fin 2, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) = 1 := by
        intro k
        obtain ⟨x, hx, hxk⟩ := hin.lemma_6_3 hC i k
        refine le_antisymm ?_ (one_le_pRank_factor hyp k)
        rw [← hxk, pRank_map_conj]
        omega
      have hcall : ∀ k : Fin 2, c k = c i := by
        intro k
        have hk : k = i ∨ k = j := by omega
        rcases hk with rfl | rfl
        · rfl
        · exact hcij.symm
      refine Or.inr ⟨rfl, fun i' j' hij' => ⟨canonical_two_factor_product D Abar hyp.hcomm
        hyp.hgen i' j' hij', hrank i', ?_⟩⟩
      intro a₁ ha₁ a₂ ha₂ ha₁2 ha₂2 hcomm12 _ _
      left
      have ha₁D : a₁ ∈ D := preimage_le D _ ha₁
      have ha₂D : a₂ ∈ D := preimage_le D _ ha₂
      have hq₁ : QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨a₁, ha₁D⟩ = c i := by
        rw [← hcall i']
        exact hc.unique i' _ ((mem_preimage_iff D _ ⟨a₁, ha₁D⟩).mp ha₁)
          (orderOf_mk_eq_two ha₁2)
      have hq₂ : QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨a₂, ha₂D⟩ = c i := by
        rw [← hcall j']
        exact hc.unique j' _ ((mem_preimage_iff D _ ⟨a₂, ha₂D⟩).mp ha₂)
          (orderOf_mk_eq_two ha₂2)
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
    · exact step_two hin hC h hc hij hj hcij

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5

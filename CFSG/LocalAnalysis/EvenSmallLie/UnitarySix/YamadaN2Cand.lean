module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Span
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Good

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem prod_expand (Y Δ : ℕ → Mat18) (l : List ℕ) (hY : ∀ n ∈ l, FixV1 (Y n))
    (hR : ∀ n ∈ l, RowV1 (Δ n)) (hC : ∀ n ∈ l, ColNV1 (Δ n)) :
    (l.map fun n => Y n + Δ n).prod = (l.map Y).prod +
      ∑ i ∈ Finset.range l.length, Δ (l.getD i 0) * ((l.drop (i + 1)).map Y).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih (fun n hn => hY n (by simp [hn]))
      (fun n hn => hR n (by simp [hn])) (fun n hn => hC n (by simp [hn])), List.length_cons,
      Finset.sum_range_succ', List.map_cons, List.prod_cons]
    simp only [List.getD_cons_succ, List.drop_succ_cons, List.getD_cons_zero, List.drop_zero]
    have h1 : Y a * ∑ i ∈ Finset.range l.length, Δ (l.getD i 0) * ((l.drop (i + 1)).map Y).prod =
        ∑ i ∈ Finset.range l.length, Δ (l.getD i 0) * ((l.drop (i + 1)).map Y).prod := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : l.getD i 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _
      rw [← mul_assoc, fixV1_mul_rowV1 (hY a (by simp)) (hR _ (List.mem_cons_of_mem a hi'))]
    have h2 : Δ a * ∑ i ∈ Finset.range l.length, Δ (l.getD i 0) * ((l.drop (i + 1)).map Y).prod =
        0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : l.getD i 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _
      rw [← mul_assoc, colNV1_mul_rowV1 (hC a (by simp)) (hR _ (List.mem_cons_of_mem a hi')),
        zero_mul]
    rw [add_mul, mul_add, mul_add, h1, h2, add_zero]
    abel

theorem layer2_eqA {X Y Δ T E : Mat18} (hX : X = Y + Δ) (hY : FixV1 Y) (hR : RowV1 Δ)
    (hC : ColNV1 Δ) (hT : PresV1 T) (h : X * (T * X * T) = E) :
    Δ * (T * Y * T) + T * Δ * T = E + Y * (T * Y * T) := by
  have hTΔT : RowV1 (T * Δ * T) := rowV1_mul (presV1_mul_rowV1 hT hR) T
  have h1 : Y * (T * Δ * T) = T * Δ * T := fixV1_mul_rowV1 hY hTΔT
  have h2 : Δ * (T * Δ * T) = 0 := colNV1_mul_rowV1 hC hTΔT
  rw [hX, show T * (Y + Δ) * T = T * Y * T + T * Δ * T by noncomm_ring, mul_add, add_mul,
    add_mul, h1, h2, add_zero] at h
  rw [← h]
  have : ∀ A B C : Mat18, B + C = A + B + C + A := by
    intro A B C; rw [show A + B + C + A = (A + A) + B + C by abel, matN_add_self, zero_add]
  exact this _ _ _

theorem lamZ_lt (z j m : ℕ) : lamZ z j m < 16 := by
  rw [lamZ, lamMaskOf]; exact Nat.mod_lt _ (by norm_num)

theorem dLin2_cand {z : ℕ} (hz : z < 4) (k : Fin 20) :
    dLin2 (fun s : Fin 5 => candM z s) k = if (k : ℕ) < 4 then aM2 k else 0 := by
  have h1 := congrArg (toVec (20 * 64)) (dCheck2_cand hz)
  rw [toVec_dFb2, dTarget2_vec] at h1
  have h2 := congrArg (blocksOf 20) h1
  simp only [dF2, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_apply,
    blocksEquiv_symm_apply, blocksOf_vecOf] at h2
  rw [blocksOf_packBlks8] at h2
  exact congrFun h2 k

theorem cand_hν {z : ℕ} (hz : z < 4) {j m : ℕ} (hj : j < 4)
    (hm : m < 4) : n0M2 j * candM z m * n1M2 j + msum8 4 (cMask2 j m) (candM z) +
      msum8 4 (lamZ z j m) aM2 = 0 := by
  have h := dLin2_cand hz ⟨4 + 4 * j + m, by omega⟩
  change dBlockM2 (ext5M fun s : Fin 5 => candM z s) (4 + 4 * j + m) = _ at h
  have hk1 : ¬ (4 + 4 * j + m < 4) := by omega
  have hj' : (4 + 4 * j + m - 4) / 4 = j := by omega
  have hm' : (4 + 4 * j + m - 4) % 4 = m := by omega
  have hext : ∀ n < 5, ext5M (fun s : Fin 5 => candM z s) n = candM z n := fun n hn => by
    simp [ext5M, hn]
  rw [dBlockM2, ite_eq_right hk1, hj', hm', ite_eq_right (show ¬ (4 + 4 * j + m < 4) from hk1)]
    at h
  rw [hext m (by omega), msum8_eq_of_lt (g := candM z) fun n hn => hext n (by omega), hext 4
    (by omega)] at h
  have hl : ∑ q ∈ Finset.range 4, lamOfM (candM z 4) j m q • aM2 q = msum8 4 (lamZ z j m) aM2 := by
    rw [msum8]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [candM, ← bz_lamMaskOf _ hj hm (Finset.mem_range.mp hq)]
    rfl
  rw [hl] at h
  exact h

theorem mx_dProd {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)} {π : Γ →* (W →ₗ[ZMod 2] W)}
    (d : ℕ → Γ) (ν : ℕ) :
    matOfN e (π (dProd d ν)) = ((bitList ν).map fun n => matOfN e (π (d n))).prod := by
  rw [dProd, map_list_prod]
  change matHomN e _ = _
  rw [map_list_prod, List.map_map, List.map_map]
  rfl

section Layer2

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem cls_cases (r : Fin 18) : clsN r = 0 ∨ clsN r = 1 ∨ clsN r = 2 := by
  have := clsN_le r; omega

theorem R3bHyp.supp_delta (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {x : Γ} (hx : x ∈ D) {z n : ℕ} (hz : z < 4)
    (hn : n < 4) (hβ : betaG e π x = candM z n) (r c : Fin 18)
    (hrc : ¬ (clsN r = 0 ∧ clsN c ≠ 0)) : (matOfN e (π x) - yM z n) r c = 0 := by
  have hf := h.flagM hK hx
  rw [Matrix.sub_apply]
  by_cases h12 : clsN r = 1 ∧ clsN c = 2
  · obtain ⟨i, rfl⟩ := exists_w0pF h12.1
    obtain ⟨j, rfl⟩ := exists_w1F h12.2
    have h1 := congrFun (congrFun hβ i) j
    have h2 := congrFun (congrFun (blk1M_yM hz hn) i) j
    simp only [betaG, blk1M, Matrix.of_apply] at h1 h2
    rw [h1, ← h2, sub_self]
  · have hnf : ¬ ((clsN r ≤ 1 ∧ clsN c = 2) ∨ (clsN r = 0 ∧ clsN c = 1)) := by
      rcases cls_cases r with hr | hr | hr <;> rcases cls_cases c with hc | hc | hc <;> omega
    have h1 := hf r c hnf
    rw [Matrix.sub_apply, sub_eq_zero] at h1
    rw [h1, lay1_yM hz hn r c h12, sub_self]

theorem R3bHyp.layer2 (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {z : ℕ} (hz : z < 4) {d : ℕ → Γ}
    (hd : ∀ n < 4, d n ∈ D) (hdτ : ∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n)))
    (hβ : ∀ n < 4, betaG e π (d n) = candM z n)
    (hν : ∀ j < 4, ∀ m < 4, θ (gen3 (nuS j)) * d m * (θ (gen3 (nuS j)))⁻¹ =
      dProd d (cMask2 j m) * eProdG θ (lamZ z j m)) :
    z < 2 ∧ ∀ n < 4, matOfN e (π (d n)) = toMat 18 18 (candXBits z n) := by
  set X : ℕ → Mat18 := fun n => matOfN e (π (d n)) with hXdef
  set Δ : ℕ → Mat18 := fun n => X n - yM z n with hΔdef
  have hΔe : ∀ n < 4, Δ n = emb2M (blk2M (Δ n)) := fun n hn =>
    eq_emb2M fun r c hrc => h.supp_delta hK (hd n hn) hz hn (hβ n hn) r c hrc
  have hR : ∀ n < 4, RowV1 (Δ n) := fun n hn => by rw [hΔe n hn]; exact rowV1_emb2M _
  have hC : ∀ n < 4, ColNV1 (Δ n) := fun n hn => by rw [hΔe n hn]; exact colNV1_emb2M _
  have hX : ∀ n, X n = yM z n + Δ n := fun n => by simp only [hΔdef]; abel
  set δ : Fin 128 → ZMod 2 := fun k => blk2M (Δ ((k : ℕ) / 32)) ⟨(k : ℕ) % 32,
    Nat.mod_lt _ (by norm_num)⟩ with hδdef
  have hds : ∀ m < 4, emb2M (dsOf δ m) = Δ m := fun m hm => by
    rw [hΔe m hm]
    congr 1
    ext i
    simp only [dsOf, hδdef]
    rw [dite_eq_left (by omega)]
    have h1 : (32 * m + (i : ℕ)) / 32 = m := by omega
    have h2 : (⟨(32 * m + (i : ℕ)) % 32, Nat.mod_lt _ (by norm_num)⟩ : Fin 32) = i :=
      Fin.ext (by simp)
    simp only [h1, h2]
  have hA : ∀ k < 4, Δ k * (tauM * yM z k * tauM) + tauM * Δ k * tauM =
      eM k + yM z k * (tauM * yM z k * tauM) := fun k hk => by
    have e1 := congrArg (fun x => matOfN e (π x)) (hdτ k hk)
    simp only [mx_mul, h.mx_τ he, mx_E hK] at e1
    exact layer2_eqA (hX k) (fixV1_yM hz hk) (hR k hk) (hC k hk) presV1_tauM
      (by rw [← mul_assoc] at e1; simpa [hXdef, mul_assoc] using e1)
  have hB : ∀ j < 4, ∀ m < 4, vM j * Δ m * vM j +
      ∑ i ∈ Finset.range (bitList (cMask2 j m)).length, Δ ((bitList (cMask2 j m)).getD i 0) *
        (yProdM z ((bitList (cMask2 j m)).drop (i + 1)) * eProdM (lamZ z j m)) =
      yProdM z (bitList (cMask2 j m)) * eProdM (lamZ z j m) + vM j * yM z m * vM j := by
    intro j hj m hm
    have e1 := congrArg (fun x => matOfN e (π x)) (hν j hj m hm)
    simp only [← map_inv θ, gen3_inv, mx_mul, mx_V hK, mx_dProd, mx_eProdG hK] at e1
    have hl : ∀ n ∈ bitList (cMask2 j m), n < 4 := fun n hn => bitList_lt hn
    have e2 : (List.map (fun n => matOfN e (π (d n))) (bitList (cMask2 j m))).prod =
        ((bitList (cMask2 j m)).map fun n => yM z n + Δ n).prod :=
      congrArg List.prod (List.map_congr_left fun n _ => hX n)
    rw [e2, prod_expand (yM z) Δ _ (fun n hn => fixV1_yM hz (hl n hn))
      (fun n hn => hR n (hl n hn)) (fun n hn => hC n (hl n hn)), show matOfN e (π (d m)) = X m
      from rfl, hX m] at e1
    rw [add_mul, mul_add, add_mul, Finset.sum_mul] at e1
    simp only [yProdM_eq, mul_assoc] at e1 ⊢
    have key : ∀ A B C Dd : Mat18, A + B = C + Dd → B + Dd = C + A := by
      intro A B C Dd hABCD
      calc B + Dd = (A + B) + (A + Dd) := by
            rw [show (A + B) + (A + Dd) = (A + A) + B + Dd by abel, matN_add_self, zero_add]
        _ = (C + Dd) + (A + Dd) := by rw [hABCD]
        _ = C + A := by
            rw [show (C + Dd) + (A + Dd) = C + A + (Dd + Dd) by abel, matN_add_self, add_zero]
    exact key _ _ _ _ e1
  have hk : ∀ k < 20, s2OutM z (fun m => emb2M (dsOf δ m)) k = tgtM z k := by
    intro k hk20
    unfold s2OutM tgtM
    dsimp only
    split_ifs with hk4
    · rw [hds k hk4]; exact hA k hk4
    · have hj : (k - 4) / 4 < 4 := by omega
      have hm : (k - 4) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      unfold linEM
      dsimp only
      rw [hds _ hm]
      rw [← hB _ hj _ hm]
      refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i hi => ?_)
      have hmem : (bitList (cMask2 ((k - 4) / 4) ((k - 4) % 4))).getD i 0 ∈
          bitList (cMask2 ((k - 4) / 4) ((k - 4) % 4)) := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _
      rw [hds _ (bitList_lt hmem)]
  have hS2 : S2 z δ = tgtV z := by
    ext idx
    simp only [S2, LinearMap.coe_mk, AddHom.coe_mk, tgtV]
    rw [hk _ (by omega)]
  have hz2 : z < 2 := by
    by_contra hz2
    exact S2_ne_tgtV (by omega) hz δ hS2
  have hδ := eq_of_S2_eq hz2 hS2
  refine ⟨hz2, fun n hn => ?_⟩
  rw [show matOfN e (π (d n)) = X n from rfl, hX n, ← hds n hn, hδ,
    ← toMat_emb2m (s2Sol_lt z), yM, ← toMat_bxor]
  rfl

theorem R3bHyp.layer1 (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) :
    ∃ z < 4, ∃ d : ℕ → Γ, (∀ n < 4, d n ∈ D) ∧
      (∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n))) ∧
      (∀ n < 4, betaG e π (d n) = candM z n) ∧
      ∀ j < 4, ∀ m < 4, θ (gen3 (nuS j)) * d m * (θ (gen3 (nuS j)))⁻¹ =
        dProd d (cMask2 j m) * eProdG θ (lamZ z j m) := by
  have hex : ∀ n, ∃ x : Γ, n < 4 → x ∈ D ∧ x * τ x = θ (gen3 (Fin.ofNat 12 n)) := fun n => by
    by_cases hn : n < 4
    · obtain ⟨x, hx, hxτ⟩ := h.τsurj n hn
      exact ⟨x, fun _ => ⟨hx, hxτ⟩⟩
    · exact ⟨1, fun h' => absurd h' hn⟩
  choose d₀ hd₀ using hex
  have hd₀D : ∀ n < 4, d₀ n ∈ D := fun n hn => (hd₀ n hn).1
  have hd₀τ : ∀ n < 4, d₀ n * τ (d₀ n) = θ (gen3 (Fin.ofNat 12 n)) := fun n hn => (hd₀ n hn).2
  have hrel : ∀ j m, ∃ μ : ℕ, j < 4 → m < 4 → μ < 16 ∧
      n0M2 j * betaG e π (d₀ m) * n1M2 j + (msum8 4 (cMask2 j m) fun n => betaG e π (d₀ n)) +
        msum8 4 μ aM2 = 0 := fun j m => by
    by_cases hjm : j < 4 ∧ m < 4
    · obtain ⟨μ, hμ, -, hβ⟩ := h.nu_rel he hK hd₀D hd₀τ hjm.1 hjm.2
      exact ⟨μ, fun _ _ => ⟨hμ, hβ⟩⟩
    · exact ⟨0, fun hj hm => absurd ⟨hj, hm⟩ hjm⟩
  choose μ₀ hμ₀ using hrel
  obtain ⟨z, hz, hcand⟩ := exists_candidate2 (fun i : Fin 4 => betaG e π (d₀ i))
    (fun j m q => bz ((μ₀ j m).testBit q))
    (fun i => by
      have := h.delta_d he hK hd₀D hd₀τ i.isLt
      rw [deltaM] at this; exact this)
    (fun j m => by
      have h1 := (hμ₀ j m j.isLt m.isLt).2
      rw [msum8_eq_of_lt (f := fun n => betaG e π (d₀ n))
        (g := fun n => if h : n < 4 then betaG e π (d₀ (⟨n, h⟩ : Fin 4)) else 0)
        fun n hn => by rw [dite_eq_left hn]] at h1
      have h2 : msum8 4 (μ₀ j m) aM2 = ∑ q : Fin 4, bz ((μ₀ j m).testBit q) • aM2 q := by
        rw [msum8, Finset.sum_range (fun q => bz ((μ₀ j m).testBit q) • aM2 q)]
      rw [h2] at h1
      exact h1)
  have hmask : ∀ n, ∃ μ : ℕ, n < 4 → μ < 16 ∧
      msum8 4 μ aM2 = betaG e π (d₀ n) + candM z n := fun n => by
    by_cases hn : n < 4
    · obtain ⟨μ, hμ, hμe⟩ := exists_mask_of_mem (hcand ⟨n, hn⟩)
      exact ⟨μ, fun _ => ⟨hμ, hμe⟩⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose μ₁ hμ₁ using hmask
  set d₁ : ℕ → Γ := fun n => d₀ n * eProdG θ (μ₁ n) with hd₁def
  have hd₁D : ∀ n < 4, d₁ n ∈ D := fun n hn => mul_mem (hd₀D n hn) (eProdG_mem h _)
  have hd₁τ : ∀ n < 4, d₁ n * τ (d₁ n) = θ (gen3 (Fin.ofNat 12 n)) := fun n hn => by
    have hE := eProdG_mem h (μ₁ n)
    have hτE := h.τ_eProdG (μ₁ n)
    simp only [hd₁def, map_mul, hτE]
    calc d₀ n * eProdG θ (μ₁ n) * (τ (d₀ n) * eProdG θ (μ₁ n))
        = d₀ n * τ (d₀ n) * (eProdG θ (μ₁ n) * eProdG θ (μ₁ n)) := by
          rw [show d₀ n * eProdG θ (μ₁ n) * (τ (d₀ n) * eProdG θ (μ₁ n)) =
            d₀ n * (eProdG θ (μ₁ n) * τ (d₀ n)) * eProdG θ (μ₁ n) by group,
            h.D_comm _ hE _ (h.τD _ (hd₀D n hn))]
          group
      _ = θ (gen3 (Fin.ofNat 12 n)) := by rw [h.D_sq _ hE, mul_one, hd₀τ n hn]
  have hβ₁ : ∀ n < 4, betaG e π (d₁ n) = candM z n := fun n hn => by
    rw [hd₁def, h.beta_mul hK (hd₀D n hn) (eProdG_mem h _), h.beta_eProdG hK, (hμ₁ n hn).2,
      ← add_assoc, mat8_add_self', zero_add]
  refine ⟨z, hz, d₁, hd₁D, hd₁τ, hβ₁, fun j hj m hm => ?_⟩
  obtain ⟨μ, hμ, hx, hβ⟩ := h.nu_rel he hK hd₁D hd₁τ hj hm
  rw [hβ₁ m hm, msum8_eq_of_lt (g := candM z) fun n hn => hβ₁ n hn] at hβ
  have hc := cand_hν hz hj hm
  have : msum8 4 μ aM2 = msum8 4 (lamZ z j m) aM2 :=
    (eq_of_add_eq_zero8 hβ).symm.trans (eq_of_add_eq_zero8 hc)
  rw [hx, eq_of_msum8_eq hμ (lamZ_lt z j m) this]

end Layer2

section Main

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ}

theorem R3bHyp.exists_cands [Finite W] (h : R3bHyp π θ τW ι D W₀ V τ) :
    ∃ (e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)) (z : ℕ), z < 2 ∧ matOfN e τW = tMN 9 ∧
      (∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) ∧ ∃ d : ℕ → Γ, (∀ n < 4, d n ∈ D) ∧
      (∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n))) ∧
      (∀ n < 4, betaG e π (d n) = candM z n) ∧
      (∀ n < 4, matOfN e (π (d n)) = toMat 18 18 (candXBits z n)) ∧
      ∀ x ∈ D, ∃ μ < 16, ∃ ν < 16, x = dProd d ν * eProdG θ μ := by
  obtain ⟨e, he, hK⟩ := exists_good_coords18 π θ τW ι h.inj h.fix h.range h.card
    (fun g x => h.comm g x) h.ι_eq
  obtain ⟨z, hz, d, hd, hdτ, hβ, hν⟩ := h.layer1 he hK
  obtain ⟨hz2, hX⟩ := h.layer2 he hK hz hd hdτ hβ hν
  exact ⟨e, z, hz2, he, hK, d, hd, hdτ, hβ, hX, fun x hx => h.exists_span he hK hd hdτ hx⟩

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaN2

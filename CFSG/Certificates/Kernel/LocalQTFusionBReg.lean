module

public import CFSG.Certificates.Kernel.LocalQTFusionSReg

public section

namespace CFSG.KC.LQT.FB.Reg

open CFSG.KC.LQT.BSP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BC CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Lin2 CFSG.QuasithinUnique.Lin2.RankCert CFSG.QuasithinUnique.Lin2.FusionCert
open CFSG.KC.LQT.FS.Reg

structure OrderW (n r : Nat) (G : List (Array Nat)) (M : Nat) (U : Nat → List Nat)
    (par : Nat → Nat) (cl : Nat → Nat → Nat) : Prop where
  key : ∀ a < M, ∀ b < M, keyNat n r (U a) = keyNat n r (U b) → a = b
  step : ∀ i < M, ∀ t < G.length, cl i t < M ∧ U (cl i t) = applyTab G[t]! (U i)
  par_spec : ∀ k < M, 0 < k → par k < k ∧ ∃ t < G.length, cl (par k) t = k

structure SetupW (n r M : Nat) (G : List (Array Nat)) (U : Nat → List Nat) (par : Nat → Nat)
    (cl : Nat → Nat → Nat) (Pt : List Nat) : Prop where
  hO : OrderW n r G M U par cl
  hM : 0 < M
  hUv : ∀ i < M, Val n Pt.length (U i)
  hU0 : U 0 = Pt
  hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n
  hGinj : ∀ t < G.length, ∀ x < n, ∀ y < n, img G[t]! x = img G[t]! y → x = y
  hPtr : ∀ t < G.length, ∀ x ∈ Pt.take r, img G[t]! x ∈ Pt

section Words

variable {n r M : Nat} {G : List (Array Nat)} {U : Nat → List Nat} {par : Nat → Nat}
  {cl : Nat → Nat → Nat} {Pt : List Nat}

theorem semW (S : SetupW n r M G U par cl Pt) {φ f : Nat → Nat} (hw : Wd G cl n M φ f) :
    (∀ x < n, f x < n) ∧ (∀ x < n, ∀ y < n, f x = f y → x = y) ∧
      ∀ i < M, φ i < M ∧ U (φ i) = (U i).map f := by
  induction hw with
  | one => exact ⟨fun x hx => hx, fun x _ y _ e => e, fun i hi => ⟨hi, by simp⟩⟩
  | gen t ht =>
    refine ⟨S.hGlt t ht, S.hGinj t ht, fun i hi => ?_⟩
    obtain ⟨h1, h2⟩ := S.hO.step i hi t ht
    exact ⟨h1, h2⟩
  | comp _ _ ih1 ih2 =>
    obtain ⟨a1, a2, a3⟩ := ih1
    obtain ⟨b1, b2, b3⟩ := ih2
    refine ⟨fun x hx => a1 _ (b1 x hx), fun x hx y hy e => b2 x hx y hy (a2 _ (b1 x hx) _ (b1 y hy) e),
      fun i hi => ?_⟩
    obtain ⟨c1, c2⟩ := b3 i hi
    obtain ⟨d1, d2⟩ := a3 _ c1
    refine ⟨d1, ?_⟩
    simp only [Function.comp_apply]
    rw [d2, c2, List.map_map]
  | ext hφ hf _ ih =>
    obtain ⟨a1, a2, a3⟩ := ih
    refine ⟨fun x hx => by rw [hf x hx]; exact a1 x hx,
      fun x hx y hy e => a2 x hx y hy (by rw [← hf x hx, ← hf y hy]; exact e), fun i hi => ?_⟩
    obtain ⟨b1, b2⟩ := a3 i hi
    refine ⟨by rw [hφ i hi]; exact b1, ?_⟩
    rw [hφ i hi, b2]
    exact List.map_congr_left fun x hx => (hf x ((S.hUv i hi).2 x hx)).symm

theorem orderW (S : SetupW n r M G U par cl Pt) {φ f : Nat → Nat} (hw : Wd G cl n M φ f) :
    ∃ m, 0 < m ∧ ∀ i < M, φ^[m] i = i := by
  obtain ⟨h1, h2, h3⟩ := semW S hw
  refine iter_order (fun i hi => (h3 i hi).1) (fun a ha b hb e => ?_)
  have e1 : U (φ a) = U (φ b) := by rw [e]
  rw [(h3 a ha).2, (h3 b hb).2] at e1
  have e2 := map_inj_on h2 (fun x hx => (S.hUv a ha).2 x hx) (fun x hx => (S.hUv b hb).2 x hx) e1
  exact S.hO.key a ha b hb (by rw [e2])

theorem fix_genW (S : SetupW n r M G U par cl Pt) {κ f : Nat → Nat} (hw : Wd G cl n M κ f)
    (h0 : κ 0 = 0) {t : Nat} (ht : t < G.length) : κ (cl 0 t) = cl 0 t := by
  obtain ⟨h1, h2, h3⟩ := semW S hw
  have hk := (h3 0 S.hM).2
  rw [h0, S.hU0] at hk
  have hfix := map_fix hk
  obtain ⟨hj1, hj2⟩ := S.hO.step 0 S.hM t ht
  obtain ⟨hk1, hk2⟩ := h3 _ hj1
  refine S.hO.key _ hk1 _ hj1 ?_
  rw [keyNat_eq_iff (S.hUv _ hk1) (S.hUv _ hj1), hk2, hj2, S.hU0, applyTab, List.map_map,
    ← List.map_take, ← List.map_take]
  exact List.map_congr_left fun x hx => hfix _ (S.hPtr t ht x hx)

theorem reg_fixW (S : SetupW n r M G U par cl Pt) :
    ∀ k, k < M → ∀ {κ f : Nat → Nat}, Wd G cl n M κ f → κ 0 = 0 → κ k = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk κ f hw h0
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact h0
    obtain ⟨hp, t, ht, hct⟩ := S.hO.par_spec k hk hk0
    have hσ : Wd G cl n M (fun i => cl i t) (img G[t]!) := Wd.gen t ht
    obtain ⟨m, hm, hmo⟩ := orderW S hσ
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hκ' := Wd.comp (hσ.iter m') (Wd.comp hw hσ)
    have e1 : ∀ y, (fun i => cl i t)^[m'] ((fun i => cl i t) y) = (fun i => cl i t)^[m'.succ] y :=
      fun y => (Function.iterate_succ_apply _ _ _).symm
    have hκ'0 : ((fun i => cl i t)^[m'] ∘ (κ ∘ fun i => cl i t)) 0 = 0 := by
      simp only [Function.comp_apply]
      rw [fix_genW S hw h0 ht, e1]
      exact hmo 0 S.hM
    have h1 := ih (par k) hp (by omega) hκ' hκ'0
    simp only [Function.comp_apply] at h1
    rw [hct] at h1
    obtain ⟨-, -, h3⟩ := semW S hw
    have hκk := (h3 k hk).1
    have h4 : (fun i => cl i t)^[m'.succ] (κ k) = k := by
      rw [Function.iterate_succ_apply']
      show cl _ t = k
      rw [h1]
      exact hct
    rw [hmo _ hκk] at h4
    exact h4

theorem regW (S : SetupW n r M G U par cl Pt) {ψ f χ h : Nat → Nat}
    (hψ : Wd G cl n M ψ f) (hχ : Wd G cl n M χ h) (h0 : ψ 0 = χ 0) : ∀ k < M, ψ k = χ k := by
  intro k hk
  obtain ⟨m, hm, hmo⟩ := orderW S hχ
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hκ := Wd.comp (hχ.iter m') hψ
  have h1 : (χ^[m'] ∘ ψ) 0 = 0 := by
    simp only [Function.comp_apply]
    rw [h0, ← Function.iterate_succ_apply]
    exact hmo 0 S.hM
  have h2 := reg_fixW S k hk hκ h1
  simp only [Function.comp_apply] at h2
  obtain ⟨-, -, h3⟩ := semW S hψ
  have h4 : χ^[m'.succ] (ψ k) = χ k := by
    rw [Function.iterate_succ_apply', h2]
  rw [hmo _ (h3 k hk).1] at h4
  exact h4

end Words

section Index

variable {n r M : Nat} {G : List (Array Nat)} {U : Nat → List Nat} {par : Nat → Nat}
  {cl : Nat → Nat → Nat} {Pt : List Nat} {parA clA : Array Nat}

theorem genIdx_specW (S : SetupW n r M G U par cl Pt) (hpar : ∀ k < M, 0 < k → parA[k]! = par k)
    (hclA : ∀ i < M, ∀ t < G.length, clA[i * (G.length + G.length) + t]! = cl i t) {i : Nat}
    (hi : i < M) (hi0 : 0 < i) :
    genIdx G.length G.length parA clA i < G.length ∧
      cl (par i) (genIdx G.length G.length parA clA i) = i := by
  obtain ⟨hp, t, ht, hct⟩ := S.hO.par_spec i hi hi0
  have hpM : par i < M := by omega
  have hex : ∃ j ∈ List.range G.length,
      (clA[parA[i]! * (G.length + G.length) + j]! == i) = true := by
    refine ⟨t, List.mem_range.2 ht, ?_⟩
    rw [hpar i hi hi0, hclA _ hpM t ht, hct]
    simp
  have hsome := List.find?_isSome.2 hex
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hsome
  have h1 := List.find?_some hj
  have h2 := List.mem_of_find?_eq_some hj
  have hjg := List.mem_range.1 h2
  have e : genIdx G.length G.length parA clA i = j := by
    rw [genIdx, hj]
    rfl
  rw [e]
  refine ⟨hjg, ?_⟩
  rw [hpar i hi hi0, hclA _ hpM j hjg] at h1
  simpa using h1

theorem idxTab_propW (S : SetupW n r M G U par cl Pt) (hpar : ∀ k < M, 0 < k → parA[k]! = par k)
    (hclA : ∀ i < M, ∀ t < G.length, clA[i * (G.length + G.length) + t]! = cl i t)
    (hGsz : ∀ t < G.length, G[t]!.size = n) :
    ∀ f i, i < M → (idxTab n G G.length G.length parA clA f i).size = n ∧
      ∀ q < n, img (idxTab n G G.length G.length parA clA f i) q < n := by
  intro f
  induction f with
  | zero =>
    intro i _
    simp only [idxTab]
    exact ⟨Array.size_range, fun q hq => by rw [img_range' hq]; exact hq⟩
  | succ f ih =>
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simp only [idxTab, if_true]
      exact ⟨Array.size_range, fun q hq => by rw [img_range' hq]; exact hq⟩
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hg, -⟩ := genIdx_specW S hpar hclA hi hpos
      have hpi := (S.hO.par_spec i hi hpos).1
      have e : idxTab n G G.length G.length parA clA (f + 1) i =
          compArr (G.getD (genIdx G.length G.length parA clA i) #[])
            (idxTab n G G.length G.length parA clA f parA[i]!) := by
        simp [idxTab, hi0]
      rw [e, getD_gen G hg, hpar i hi hpos]
      obtain ⟨h1, h2⟩ := ih (par i) (by omega)
      refine ⟨by simp [compArr, h1], fun q hq => ?_⟩
      rw [img_compArr (hGsz _ hg) h1 h2 hq]
      exact S.hGlt _ hg _ (h2 q hq)

theorem word_idxW (S : SetupW n r M G U par cl Pt) (hpar : ∀ k < M, 0 < k → parA[k]! = par k)
    (hclA : ∀ i < M, ∀ t < G.length, clA[i * (G.length + G.length) + t]! = cl i t)
    (hGsz : ∀ t < G.length, G[t]!.size = n) :
    ∀ f i, i ≤ f → i < M →
      Wd G cl n M (fun k => mulIdx G.length G.length parA clA f i k)
        (img (idxTab n G G.length G.length parA clA f i)) := by
  intro f
  induction f with
  | zero =>
    intro i hif hi
    obtain rfl : i = 0 := by omega
    refine Wd.ext (ψ := id) (h := id) (fun k _ => ?_) (fun x hx => ?_) Wd.one
    · simp [mulIdx]
    · simp only [idxTab]
      rw [img_range' hx]
      rfl
  | succ f ih =>
    intro i hif hi
    by_cases hi0 : i = 0
    · subst hi0
      refine Wd.ext (ψ := id) (h := id) (fun k _ => ?_) (fun x hx => ?_) Wd.one
      · simp [mulIdx]
      · simp only [idxTab, if_true]
        rw [img_range' hx]
        rfl
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hg, hcl⟩ := genIdx_specW S hpar hclA hi hpos
      have hpi := (S.hO.par_spec i hi hpos).1
      have hih := ih (par i) (by omega) (by omega)
      rw [← hpar i hi hpos] at hih
      have hsem := (semW S hih).2.2
      refine Wd.ext (ψ := (fun j => cl j (genIdx G.length G.length parA clA i)) ∘
        (fun k => mulIdx G.length G.length parA clA f parA[i]! k))
        (h := img G[genIdx G.length G.length parA clA i]! ∘
          img (idxTab n G G.length G.length parA clA f parA[i]!)) (fun k hk => ?_) (fun x hx => ?_)
        (Wd.comp (Wd.gen _ hg) hih)
      · have e : mulIdx G.length G.length parA clA (f + 1) i k =
            clA[mulIdx G.length G.length parA clA f parA[i]! k * (G.length + G.length) +
              genIdx G.length G.length parA clA i]! := by
          simp [mulIdx, hi0]
        rw [e, hclA _ (hsem k hk).1 _ hg]
        rfl
      · have e : idxTab n G G.length G.length parA clA (f + 1) i =
            compArr (G.getD (genIdx G.length G.length parA clA i) #[])
              (idxTab n G G.length G.length parA clA f parA[i]!) := by
          simp [idxTab, hi0]
        obtain ⟨h1, h2⟩ := idxTab_propW S hpar hclA hGsz f (par i) (by omega)
        rw [← hpar i hi hpos] at h1 h2
        rw [e, getD_gen G hg, img_compArr (hGsz _ hg) h1 h2 hx]
        rfl

theorem mulIdx_zero_rightW (S : SetupW n r M G U par cl Pt)
    (hpar : ∀ k < M, 0 < k → parA[k]! = par k)
    (hclA : ∀ i < M, ∀ t < G.length, clA[i * (G.length + G.length) + t]! = cl i t) :
    ∀ f i, i ≤ f → i < M → mulIdx G.length G.length parA clA f i 0 = i := by
  intro f
  induction f with
  | zero =>
    intro i hif hi
    obtain rfl : i = 0 := by omega
    simp [mulIdx]
  | succ f ih =>
    intro i hif hi
    by_cases hi0 : i = 0
    · subst hi0
      simp [mulIdx]
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hg, hcl⟩ := genIdx_specW S hpar hclA hi hpos
      have hpi := (S.hO.par_spec i hi hpos).1
      have e : mulIdx G.length G.length parA clA (f + 1) i 0 =
          clA[mulIdx G.length G.length parA clA f parA[i]! 0 * (G.length + G.length) +
            genIdx G.length G.length parA clA i]! := by
        simp [mulIdx, hi0]
      rw [e, hpar i hi hpos, ih (par i) (by omega) (by omega), hclA _ (by omega) _ hg, hcl]

theorem U_idxW (S : SetupW n r M G U par cl Pt) (hpar : ∀ k < M, 0 < k → parA[k]! = par k)
    (hclA : ∀ i < M, ∀ t < G.length, clA[i * (G.length + G.length) + t]! = cl i t)
    (hGsz : ∀ t < G.length, G[t]!.size = n) {i : Nat} (hi : i < M) :
    U i = Pt.map (img (idxTab n G G.length G.length parA clA M i)) := by
  have hw := word_idxW S hpar hclA hGsz M i (by omega) hi
  obtain ⟨-, -, h3⟩ := semW S hw
  have := (h3 0 S.hM).2
  rw [mulIdx_zero_rightW S hpar hclA M i (by omega) hi, S.hU0] at this
  exact this

theorem c0_eq_ziW (S : SetupW n r M G U par cl Pt) (hpar : ∀ k < M, 0 < k → parA[k]! = par k)
    (hclA : ∀ i < M, ∀ t < G.length, clA[i * (G.length + G.length) + t]! = cl i t)
    (hGsz : ∀ t < G.length, G[t]!.size = n) {zi c0 : Nat} {cs : List Nat} {gws : List (List Nat)}
    (hzlt : zi < M) (hz0 : zi ≠ 0) (hc0 : c0 < M) (hcs : ∀ c ∈ cs, c = c0)
    (hcover : ∀ x < M, (((List.range G.length).all fun j =>
      mulIdx G.length G.length parA clA M clA[j]! x ==
        mulIdx G.length G.length parA clA M x clA[j]!) = false ∨ x = 0) ∨ x = zi)
    (hgw : ∀ x < G.length, evalIdxWord (mulIdx G.length G.length parA clA M) cs (gws.getD x []) =
      clA[x]!) : c0 = zi := by
  by_contra hne
  set mu := mulIdx G.length G.length parA clA M with hmu
  have h0l : ∀ k, mu 0 k = k := fun k => mulIdx_zero_left (G := G) (parA := parA) (clA := clA) S.hM k
  have hσ : ∀ j < G.length, ∃ e, clA[j]! = (fun k => mu c0 k)^[e] 0 := fun j hj => by
    obtain ⟨e, he⟩ := eval_pow c0 hcs h0l (gws.getD j [])
    exact ⟨e, by rw [← he]; exact (hgw j hj).symm⟩
  have e0 : ∀ j < G.length, clA[j]! = cl 0 j := fun j hj => by
    have := hclA 0 S.hM j hj
    rwa [Nat.zero_mul, Nat.zero_add] at this
  have hσM : ∀ j < G.length, clA[j]! < M := fun j hj => by
    rw [e0 j hj]
    exact (S.hO.step 0 S.hM j hj).1
  by_cases hc00 : c0 = 0
  · subst hc00
    have hpow : ∀ e, (fun k => mu 0 k)^[e] 0 = 0 := by
      intro e
      induction e with
      | zero => rfl
      | succ e ih => rw [Function.iterate_succ_apply', ih, h0l]
    have hzero : ∀ j < G.length, cl 0 j = 0 := fun j hj => by
      rw [← e0 j hj]
      obtain ⟨e, he⟩ := hσ j hj
      rw [he, hpow]
    have hall : ∀ k, k < M → k = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        by_contra hk0
        obtain ⟨hp, t, ht, hct⟩ := S.hO.par_spec k hk (Nat.pos_of_ne_zero hk0)
        have := ih _ hp (by omega)
        rw [this, hzero t ht] at hct
        exact hk0 hct.symm
    exact hz0 (hall zi hzlt)
  · have hφ0 : Wd G cl n M (fun k => mu c0 k)
        (img (idxTab n G G.length G.length parA clA M c0)) :=
      word_idxW S hpar hclA hGsz M c0 (by omega) hc0
    have hc00' : mu c0 0 = c0 := mulIdx_zero_rightW S hpar hclA M c0 (by omega) hc0
    rcases hcover c0 hc0 with (h | h) | h
    · have hall : ((List.range G.length).all fun j => (mu clA[j]! c0 == mu c0 clA[j]!)) = true := by
        rw [List.all_eq_true]
        intro j hj
        have hj' := List.mem_range.1 hj
        simp only [beq_iff_eq]
        obtain ⟨e, he⟩ := hσ j hj'
        have hσlt := hσM j hj'
        have hψ := word_idxW S hpar hclA hGsz M clA[j]! (by omega) hσlt
        have hχ := hφ0.iter e
        have hreg := regW S hψ hχ (by
          show mulIdx G.length G.length parA clA M clA[j]! 0 = _
          rw [mulIdx_zero_rightW S hpar hclA M _ (by omega) hσlt, ← he]) c0 hc0
        have e1 : mu c0 clA[j]! = (fun k => mu c0 k)^[e] c0 := by
          rw [he, ← Function.iterate_succ_apply' (fun k => mu c0 k) e 0, Function.iterate_succ_apply]
          show (fun k => mu c0 k)^[e] (mu c0 0) = _
          rw [hc00']
        exact hreg.trans e1.symm
      rw [hall] at h
      exact absurd h (by simp)
    · exact hc00 h
    · exact hne h

end Index

end CFSG.KC.LQT.FB.Reg

end

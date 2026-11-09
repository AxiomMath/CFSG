module

public import CFSG.Certificates.Kernel.Tower.Cls14Sound
public import Certificates.Data.Kernel.Tower.T2

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower Subgroup

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem cent16_rep (M : IsModel (⊤ : Subgroup X) n mul dec) {k GS GI LB RP : Nat}
    (hGS : ∀ i < k, l16 GS i < n) (hGI : ∀ i < k, l16 GI i < n ∧ mul (l16 GS i) (l16 GI i) = 0)
    (hP : ∀ c < n, lbG16 LB c < k ∨ c = l16 RP (lbL LB c))
    (hT : ∀ c < n, lbG16 LB c < k →
      lbL LB (mul (mul (l16 GS (lbG16 LB c)) c) (l16 GI (lbG16 LB c))) = lbL LB c ∧
        lbD16 LB (mul (mul (l16 GS (lbG16 LB c)) c) (l16 GI (lbG16 LB c))) < lbD16 LB c)
    {c : Nat} (hc : c < n) : ∃ w : X, dec c = w * dec (l16 RP (lbL LB c)) * w⁻¹ := by
  suffices H : ∀ d, ∀ c < n, lbD16 LB c = d →
      ∃ w : X, dec c = w * dec (l16 RP (lbL LB c)) * w⁻¹ from H _ c hc rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro c hc hd
    rcases hP c hc with hg | hg
    · have hgs := hGS _ hg
      obtain ⟨hl, hlt⟩ := hT c hc hg
      have hx := M.conj_lt hgs hc (hGI _ hg).1
      have hdx := M.dec_conj hgs hc (hGI _ hg).1 (hGI _ hg).2
      obtain ⟨w, hw⟩ := ih _ (hd ▸ hlt) _ hx rfl
      rw [hl, hdx] at hw
      refine ⟨(dec (l16 GS (lbG16 LB c)))⁻¹ * w, ?_⟩
      have e : dec c = (dec (l16 GS (lbG16 LB c)))⁻¹ *
          (dec (l16 GS (lbG16 LB c)) * dec c * (dec (l16 GS (lbG16 LB c)))⁻¹) *
            dec (l16 GS (lbG16 LB c)) := by group
      rw [e, hw]
      group
    · refine ⟨1, ?_⟩
      rw [one_mul, inv_one, mul_one]
      exact congrArg dec hg

theorem cent16_orbit (M : IsModel (⊤ : Subgroup X) n mul dec) {LB RP l : Nat}
    (hrep : ∀ c < n, ∃ w : X, dec c = w * dec (l16 RP (lbL LB c)) * w⁻¹)
    (hC : n ≤ Nat.card (centralizer {dec (l16 RP l)} : Subgroup X) *
      cntB n (fun c => Nat.beq (lbL LB c) l)) :
    ∀ y ∈ MulAction.orbit (ConjAct X) (dec (l16 RP l)), lbL LB (M.code y) = l := by
  classical
  obtain ⟨hfin, hX⟩ := cls16_finite M
  set F := (Finset.range n).filter fun d => Nat.beq (lbL LB d) l = true
  have hsub : (↑(F.image dec) : Set X) ⊆ MulAction.orbit (ConjAct X) (dec (l16 RP l)) := by
    intro y hy
    rw [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨w, hw⟩ := hrep d hd.1
    rw [Nat.eq_of_beq_eq_true hd.2] at hw
    refine ⟨ConjAct.toConjAct w, ?_⟩
    change ConjAct.toConjAct w • dec (l16 RP l) = dec d
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hw]
  have hinj : Set.InjOn dec ↑F := by
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    exact M.inj a ha.1 b hb.1 h
  have hF : (F.image dec).card = cntB n (fun c => Nat.beq (lbL LB c) l) := by
    rw [Finset.card_image_of_injOn hinj, cntB_eq_card]
  have hcm := card_cent_mul (dec (l16 RP l))
  rw [hX] at hcm
  have hpos : 0 < Nat.card (centralizer {dec (l16 RP l)} : Subgroup X) := Nat.card_pos
  have hle : Nat.card (MulAction.orbit (ConjAct X) (dec (l16 RP l))) ≤ (F.image dec).card := by
    rw [hF]
    refine Nat.le_of_not_lt fun hlt => ?_
    have := Nat.mul_lt_mul_of_pos_left hlt hpos
    rw [Nat.mul_comm _ (Nat.card (MulAction.orbit _ _)), hcm] at this
    omega
  have heq : (↑(F.image dec) : Set X) = MulAction.orbit (ConjAct X) (dec (l16 RP l)) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact hle
  intro y hy
  rw [← heq, Finset.coe_image, Set.mem_image] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd
  rw [M.code_dec hd.1]
  exact Nat.eq_of_beq_eq_true hd.2

theorem labOK16_of_cent (M : IsModel (⊤ : Subgroup X) n mul dec) {k GS GI LB RP nl : Nat}
    (hH : allB k (fun i => Nat.blt (l16 GI i) n && Nat.beq (mul (l16 GS i) (l16 GI i)) 0) = true)
    (hR : allB nl (fun l => Nat.blt (l16 RP l) n && Nat.beq (lbL LB (l16 RP l)) l) = true)
    (hGS : ∀ i < k, l16 GS i < n)
    (hP : ∀ c < n,
      (Nat.blt (lbL LB c) nl && (Nat.blt (lbG16 LB c) k || Nat.beq c (l16 RP (lbL LB c)))) = true)
    (hT : ∀ c < n, lbG16 LB c < k →
      lbL LB (mul (mul (l16 GS (lbG16 LB c)) c) (l16 GI (lbG16 LB c))) = lbL LB c ∧
        lbD16 LB (mul (mul (l16 GS (lbG16 LB c)) c) (l16 GI (lbG16 LB c))) < lbD16 LB c)
    (hC : ∀ l < nl, n ≤ Nat.card (centralizer {dec (l16 RP l)} : Subgroup X) *
      cntB n (fun c => Nat.beq (lbL LB c) l)) :
    labOK16 n k mul GS GI LB RP nl = true := by
  have hGI : ∀ i < k, l16 GI i < n ∧ mul (l16 GS i) (l16 GI i) = 0 := fun i hi => by
    have h1 := allB_eq_true.1 hH i hi
    rw [Bool.and_eq_true] at h1
    exact ⟨Eq.mp Nat.blt_eq h1.1, Nat.eq_of_beq_eq_true h1.2⟩
  have hP' : ∀ c < n, lbL LB c < nl ∧ (lbG16 LB c < k ∨ c = l16 RP (lbL LB c)) := fun c hc => by
    have h := hP c hc
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    refine ⟨Eq.mp Nat.blt_eq h.1, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inl (Eq.mp Nat.blt_eq h2)
    · exact Or.inr (Nat.eq_of_beq_eq_true h2)
  have hrep := fun c hc => cent16_rep M hGS hGI (fun c hc => (hP' c hc).2) hT (c := c) hc
  rw [labOK16, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hH, hR⟩, allB_eq_true.2 fun c hc => ?_⟩
  rw [labC16, Bool.and_eq_true]
  refine ⟨hP c hc, allB_eq_true.2 fun i hi => ?_⟩
  have hg := hGS i hi
  have hx := M.conj_lt hg hc (hGI i hi).1
  have hdx := M.dec_conj hg hc (hGI i hi).1 (hGI i hi).2
  obtain ⟨w, hw⟩ := hrep c hc
  have hl : lbL LB (mul (mul (l16 GS i) c) (l16 GI i)) = lbL LB c := by
    have hmem : dec (mul (mul (l16 GS i) c) (l16 GI i)) ∈
        MulAction.orbit (ConjAct X) (dec (l16 RP (lbL LB c))) := by
      refine ⟨ConjAct.toConjAct (dec (l16 GS i) * w), ?_⟩
      change ConjAct.toConjAct (dec (l16 GS i) * w) • dec (l16 RP (lbL LB c)) = _
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hdx, hw]
      group
    have h := cent16_orbit M hrep (hC _ (hP' c hc).1) _ hmem
    rwa [M.code_dec hx] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨Nat.beq_eq_true_eq _ _ ▸ hl, ?_⟩
  by_cases hi' : i = lbG16 LB c
  · right
    subst hi'
    exact Nat.blt_eq.mpr (hT c hc hi).2
  · left
    exact Bool.eq_false_iff.2 fun h => hi' (Nat.eq_of_beq_eq_true h)

theorem cent16_card_ge (M : IsModel (⊤ : Subgroup X) n mul dec) {r : Nat} (π : Nat → Nat)
    (A T : Finset Nat) (hA : ∀ a ∈ A, a < n ∧ mul a r = mul r a)
    (hT : ∀ t ∈ T, t < n ∧ mul t r = mul r t) (hTi : Set.InjOn π ↑T)
    (hπ : ∀ a ∈ A, ∀ t ∈ T, π (mul a t) = π t) (hr : r < n) :
    A.card * T.card ≤ Nat.card (centralizer {dec r} : Subgroup X) := by
  classical
  obtain ⟨hfin, -⟩ := cls16_finite M
  have hmem : ∀ c, c < n → mul c r = mul r c → dec c ∈ (centralizer {dec r} : Subgroup X) :=
    fun c hc h => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (M.comm_iff hc hr).1 h
  let f : Nat × Nat → X := fun p => dec p.1 * dec p.2
  have hinj : Set.InjOn f ↑(A ×ˢ T) := by
    rintro ⟨a, t⟩ h ⟨a', t'⟩ h' e
    rw [Finset.coe_product, Set.mem_prod] at h h'
    have ha := hA a h.1
    have ht := hT t h.2
    have ha' := hA a' h'.1
    have ht' := hT t' h'.2
    have e1 : dec (mul a t) = dec (mul a' t') := by
      rw [M.dec_mul _ ha.1 _ ht.1, M.dec_mul _ ha'.1 _ ht'.1]
      exact e
    have e2 := M.inj _ (M.mul_lt _ ha.1 _ ht.1) _ (M.mul_lt _ ha'.1 _ ht'.1) e1
    have e3 : t = t' := hTi h.2 h'.2 (by rw [← hπ a h.1 t h.2, e2, hπ a' h'.1 t' h'.2])
    subst e3
    have e4 : dec a = dec a' := mul_right_cancel e
    rw [M.inj _ ha.1 _ ha'.1 e4]
  have hsub : (↑((A ×ˢ T).image f) : Set X) ⊆ ((centralizer {dec r} : Subgroup X) : Set X) := by
    intro y hy
    rw [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨⟨a, t⟩, h, rfl⟩ := hy
    rw [Finset.mem_coe, Finset.mem_product] at h
    exact Subgroup.mul_mem _ (hmem a (hA a h.1).1 (hA a h.1).2) (hmem t (hT t h.2).1 (hT t h.2).2)
  rw [← Finset.card_product, ← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset,
    ← Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem tm_wm_pi {SM AC FA g : Nat} (hSM : ∀ s < 128, lane SM 7 127 s = s) {v t : Nat}
    (hv : v < 64) (ht : t < 16384) :
    tm (wm SM AC) FA g (2 * v) t / 128 = t / 128 ∧ tm (wm SM AC) FA g (2 * v) t % 2 = t % 2 := by
  have h1 : Nat.beq (Nat.land (2 * v) 1) 1 = false := by
    have e : Nat.land (2 * v) 1 = 0 := by
      change (2 * v) &&& 1 = 0
      rw [Nat.and_one_is_mod]
      omega
    rw [e]
    rfl
  have hv6 : Nat.shiftRight (Nat.shiftRight (2 * v) 1) 6 = 0 := by
    change (2 * v) >>> 1 >>> 6 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    omega
  have ht6 : Nat.shiftRight (Nat.shiftRight t 1) 6 = t / 128 := by
    change t >>> 1 >>> 6 = t / 128
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  have hb : Nat.land t 1 = t % 2 := Nat.and_one_is_mod t
  have hx : ∀ p q : Nat, Nat.xor (Nat.land p 63) (lane AC 6 63 q) < 64 := by
    intro p q
    have hp : Nat.land p 63 < 2 ^ 6 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
    have hq : lane AC 6 63 q < 2 ^ 6 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
    exact Nat.xor_lt_two_pow hp hq
  have hs : lane SM 7 127 (Nat.add (Nat.mul 128 0) (t / 128)) = t / 128 := by
    have e : Nat.add (Nat.mul 128 0) (t / 128) = t / 128 := by
      change 128 * 0 + t / 128 = t / 128
      omega
    rw [e]
    exact hSM _ (by omega)
  have key : tm (wm SM AC) FA g (2 * v) t = 2 * (64 * (t / 128) +
      Nat.xor (Nat.land (Nat.shiftRight (2 * v) 1) 63)
        (lane AC 6 63 (Nat.add (Nat.mul 64 0) (Nat.land (Nat.shiftRight t 1) 63)))) + t % 2 := by
    rw [tm, h1]
    dsimp only
    rw [wm, hv6, ht6, hs, hb]
    rfl
  have h64 := hx (Nat.shiftRight (2 * v) 1) (Nat.add (Nat.mul 64 0) (Nat.land (Nat.shiftRight t 1) 63))
  rw [key]
  generalize Nat.xor (Nat.land (Nat.shiftRight (2 * v) 1) 63)
    (lane AC 6 63 (Nat.add (Nat.mul 64 0) (Nat.land (Nat.shiftRight t 1) 63))) = x at h64
  omega

theorem wm_div64 (SM AC a b : Nat) :
    wm SM AC a b / 64 = lane SM 7 127 (128 * (a / 64) + b / 64) ∧ wm SM AC a b < 8192 := by
  have e1 : Nat.shiftRight a 6 = a / 64 := by
    change a >>> 6 = a / 64
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.shiftRight b 6 = b / 64 := by
    change b >>> 6 = b / 64
    rw [Nat.shiftRight_eq_div_pow]
  have key : wm SM AC a b = 64 * lane SM 7 127 (128 * (a / 64) + b / 64) +
      Nat.xor (Nat.land a 63) (lane AC 6 63 (Nat.add (Nat.mul 64 (a / 64)) (Nat.land b 63))) := by
    rw [wm, e1, e2]
    rfl
  have hL : lane SM 7 127 (128 * (a / 64) + b / 64) < 128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hp : Nat.land a 63 < 2 ^ 6 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hq : lane AC 6 63 (Nat.add (Nat.mul 64 (a / 64)) (Nat.land b 63)) < 2 ^ 6 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hx : Nat.xor (Nat.land a 63)
      (lane AC 6 63 (Nat.add (Nat.mul 64 (a / 64)) (Nat.land b 63))) < 64 :=
    Nat.xor_lt_two_pow hp hq
  rw [key]
  generalize lane SM 7 127 (128 * (a / 64) + b / 64) = L at hL ⊢
  generalize Nat.xor (Nat.land a 63)
    (lane AC 6 63 (Nat.add (Nat.mul 64 (a / 64)) (Nat.land b 63))) = z at hx ⊢
  omega

theorem tm_bit {SM AC FA g X : Nat}
    (hA : ∀ c < 16384, bit X c = Nat.xor (bit X (128 * (c / 128))) (bit X 1 * (c % 2)))
    (hB : ∀ s < 128, ∀ t < 128,
      bit X (128 * lane SM 7 127 (128 * s + t)) = Nat.xor (bit X (128 * s)) (bit X (128 * t)))
    (hC : ∀ y < 8192, l16 FA y < 8192 ∧ bit X (128 * (l16 FA y / 64)) = bit X (128 * (y / 64)))
    (hg : g < 8192) (hD : bit X (128 * (g / 64)) = 0) {x y : Nat} (hx : x < 16384)
    (hy : y < 16384) : bit X (tm (wm SM AC) FA g x y) = Nat.xor (bit X x) (bit X y) := by
  have h2 : ∀ w b, w < 8192 → b < 2 →
      bit X (2 * w + b) = Nat.xor (bit X (128 * (w / 64))) (bit X 1 * b) := by
    intro w b hw hb
    have e1 : (2 * w + b) / 128 = w / 64 := by omega
    have e2 : (2 * w + b) % 2 = b := by omega
    rw [hA _ (by omega), e1, e2]
  have hsx : Nat.shiftRight x 1 = x / 2 := by
    change x >>> 1 = x / 2
    rw [Nat.shiftRight_eq_div_pow]
  have hsy : Nat.shiftRight y 1 = y / 2 := by
    change y >>> 1 = y / 2
    rw [Nat.shiftRight_eq_div_pow]
  have hlx : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  have hly : Nat.land y 1 = y % 2 := Nat.and_one_is_mod y
  have e1 : x / 2 / 64 = x / 128 := by omega
  have e2 : y / 2 / 64 = y / 128 := by omega
  rw [hA x hx, hA y hy]
  rcases Nat.mod_two_eq_zero_or_one x with ex | ex
  · have hb : Nat.beq (Nat.land x 1) 1 = false := by
      rw [hlx, ex]
      rfl
    have key : tm (wm SM AC) FA g x y = 2 * wm SM AC (x / 2) (y / 2) + y % 2 := by
      rw [tm, hb]
      dsimp only
      rw [hsx, hsy, hly]
      rfl
    obtain ⟨hd, hw⟩ := wm_div64 SM AC (x / 2) (y / 2)
    rw [key, h2 _ _ hw (Nat.mod_lt _ (by norm_num)), hd, hB _ (by omega) _ (by omega), e1, e2, ex]
    rcases bit_cases X (128 * (x / 128)) with h1 | h1 <;>
      rcases bit_cases X (128 * (y / 128)) with h3 | h3 <;>
      rcases bit_cases X 1 with h4 | h4 <;>
      rcases Nat.mod_two_eq_zero_or_one y with h5 | h5 <;>
      simp only [h1, h3, h4, h5] <;> decide
  · have hbx : Nat.beq (Nat.land x 1) 1 = true := by
      rw [hlx, ex]
      rfl
    obtain ⟨hF, hFf⟩ := hC (y / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one y with ey | ey
    · have hby : Nat.beq (Nat.land y 1) 1 = false := by
        rw [hly, ey]
        rfl
      have key : tm (wm SM AC) FA g x y = 2 * wm SM AC (x / 2) (l16 FA (y / 2)) + 1 := by
        rw [tm, hbx, hby]
        dsimp only
        rw [hsx, hsy]
        rfl
      obtain ⟨hd, hw⟩ := wm_div64 SM AC (x / 2) (l16 FA (y / 2))
      rw [key, h2 _ _ hw (by norm_num), hd, hB _ (by omega) _ (by omega), hFf, e1, e2, ex, ey]
      rcases bit_cases X (128 * (x / 128)) with h1 | h1 <;>
        rcases bit_cases X (128 * (y / 128)) with h3 | h3 <;>
        rcases bit_cases X 1 with h4 | h4 <;>
        simp only [h1, h3, h4] <;> decide
    · have hby : Nat.beq (Nat.land y 1) 1 = true := by
        rw [hly, ey]
        rfl
      have key : tm (wm SM AC) FA g x y =
          2 * wm SM AC (wm SM AC (x / 2) (l16 FA (y / 2))) g + 0 := by
        rw [tm, hbx, hby]
        dsimp only
        rw [hsx, hsy]
        rfl
      obtain ⟨hd1, hw1⟩ := wm_div64 SM AC (x / 2) (l16 FA (y / 2))
      obtain ⟨hd2, hw2⟩ := wm_div64 SM AC (wm SM AC (x / 2) (l16 FA (y / 2))) g
      rw [key, h2 _ _ hw2 (by norm_num), hd2, hB _ (by omega) _ (by omega), hD, hd1,
        hB _ (by omega) _ (by omega), hFf, e1, e2, ex, ey]
      rcases bit_cases X (128 * (x / 128)) with h1 | h1 <;>
        rcases bit_cases X (128 * (y / 128)) with h3 | h3 <;>
        rcases bit_cases X 1 with h4 | h4 <;>
        simp only [h1, h3, h4] <;> decide

end Certificates.KernelTower

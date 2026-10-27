module

public import CFSG.Certificates.Kernel.TWLKSound
public import Certificates.Data.Kernel.TWLKF

public section

namespace CFSG.StandardType.TWLKF

open Certificates.TWLK Certificates.TWLKF Certificates.DepASmall Certificates.TwoDepSmall
open CFSG.StandardType CFSG.StandardType.TWDK CFSG.StandardType.TWLK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ}

@[expose] def ggTWSc (p N : ℕ) (a : ZMod p) : Module.End (ZMod p) (GGTWE p N) where
  toFun v j := if j.val + 2 = N then a * v j else v j
  map_add' v w := by
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem ggTWSc_apply (a : ZMod p) (v : GGTWE p N) (j : Fin (N - 1)) :
    ggTWSc p N a v j = if j.val + 2 = N then a * v j else v j := rfl

variable [Fact p.Prime]

theorem ggTWSc_inv_sc {a : ZMod p} (ha : a ≠ 0) (v : GGTWE p N) :
    ggTWSc p N a⁻¹ (ggTWSc p N a v) = v := by
  funext j
  simp only [ggTWSc_apply]
  split_ifs <;> simp [inv_mul_cancel_left₀ ha]

theorem ggTWSc_sc_inv {a : ZMod p} (ha : a ≠ 0) (v : GGTWE p N) :
    ggTWSc p N a (ggTWSc p N a⁻¹ v) = v := by
  funext j
  simp only [ggTWSc_apply]
  split_ifs <;> simp [mul_inv_cancel_left₀ ha]

theorem ggTWSc_mul_inv {a : ZMod p} (ha : a ≠ 0) : ggTWSc p N a * ggTWSc p N a⁻¹ = 1 :=
  LinearMap.ext fun v => ggTWSc_sc_inv ha v

theorem ggTWSc_inv_mul {a : ZMod p} (ha : a ≠ 0) : ggTWSc p N a⁻¹ * ggTWSc p N a = 1 :=
  LinearMap.ext fun v => ggTWSc_inv_sc ha v

theorem ggTWdot_sc (b : ZMod p) (f w : GGTWE p N) :
    ggTWdot (ggTWSc p N b f) w = ggTWdot f (ggTWSc p N b w) := by
  unfold ggTWdot ggDepAdot
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ggTWSc_apply]
  split_ifs <;> ring

theorem ggTWdot_smul_right (k : ZMod p) (f v : GGTWE p N) :
    ggTWdot f (k • v) = k * ggTWdot f v :=
  twDot_smul_right (N := N - 1) k f v

theorem ggTWSc_h (b : ZMod p) (i : Fin (N - 1)) : ggTWSc p N b (ggTWh p N i) = ggTWh p N i := by
  funext j
  simp only [ggTWSc_apply, ggTWh]
  split_ifs <;> simp

theorem ggTWSc_α (b : ZMod p) (i : Fin (N - 1)) : ggTWSc p N b (ggTWα p N i) = ggTWα p N i := by
  funext j
  simp only [ggTWSc_apply, ggTWα]
  split_ifs <;> simp

theorem ggTWSc_z (b : ZMod p) (pos : GGTWPos) : ggTWSc p N b (ggTWz p N pos) = ggTWz p N pos := by
  funext j
  cases pos <;> simp only [ggTWSc_apply, ggTWz] <;> split_ifs <;> first | omega | simp

theorem ggTWSc_x (b : ZMod p) : ggTWSc p N b (ggTWx p N) = b • ggTWx p N := by
  funext j
  simp only [ggTWSc_apply, ggTWx, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem ggTWRefl_apply (c f v : GGTWE p N) : ggTWRefl c f v = v - ggTWdot f v • c := by
  simp [ggDepARefl, ggDepAform, ggDepAdot]

theorem ggTWSc_refl {a : ZMod p} (ha : a ≠ 0) (c f : GGTWE p N) :
    ggTWSc p N a * ggTWRefl c f * ggTWSc p N a⁻¹ =
      ggTWRefl (ggTWSc p N a c) (ggTWSc p N a⁻¹ f) := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, ggTWRefl_apply, ggTWRefl_apply, map_sub,
    map_smul, ggTWSc_sc_inv ha, ggTWdot_sc]

theorem ggTWSc_frame_comm (b : ZMod p) (i : Fin (N - 1)) :
    ggTWSc p N b * ggTWRefl (ggTWh p N i) (ggTWα p N i) =
      ggTWRefl (ggTWh p N i) (ggTWα p N i) * ggTWSc p N b := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, ggTWRefl_apply, ggTWRefl_apply, map_sub,
    map_smul, ggTWSc_h, ← ggTWdot_sc, ggTWSc_α]

theorem ggTWSc_roots (b : ZMod p) {v : GGTWE p N}
    (hv : v ∈ ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N))) : ggTWSc p N b v = v := by
  obtain ⟨w, hw, c, ⟨i, rfl⟩, rfl⟩ := hv
  have hcomm : ggTWSc p N b * w = w * ggTWSc p N b := by
    induction hw using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ggTWSc_frame_comm b k
    | one => rw [mul_one, one_mul]
    | mul x y _ _ ihx ihy => rw [← mul_assoc, ihx, mul_assoc, ihy, mul_assoc]
  have h := congrArg (fun g : Module.End (ZMod p) (GGTWE p N) => g (ggTWh p N i)) hcomm
  simp only [Module.End.mul_apply, ggTWSc_h] at h
  exact h

@[expose] def ggTWScNews (p N : ℕ) (a : ZMod p) (news : Set (GGTWE p N × GGTWE p N)) :
    Set (GGTWE p N × GGTWE p N) :=
  (fun t => (ggTWSc p N a t.1, ggTWSc p N a⁻¹ t.2)) '' news

theorem ggTWSc_closure {a : ZMod p} (ha : a ≠ 0) (news : Set (GGTWE p N × GGTWE p N))
    {s' : Module.End (ZMod p) (GGTWE p N)}
    (hs' : s' ∈ Submonoid.closure (ggTWGens p N (ggTWScNews p N a news))) :
    ∃ s ∈ Submonoid.closure (ggTWGens p N news), s' = ggTWSc p N a * s * ggTWSc p N a⁻¹ := by
  induction hs' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨t, ⟨u, hu, rfl⟩, rfl⟩
    · refine ⟨ggTWRefl (ggTWh p N i) (ggTWα p N i),
        Submonoid.subset_closure (Set.mem_union_left _ ⟨i, rfl⟩), ?_⟩
      rw [ggTWSc_refl ha, ggTWSc_h, ggTWSc_α]
    · exact ⟨ggTWRefl u.1 u.2, Submonoid.subset_closure (Set.mem_union_right _ ⟨u, hu, rfl⟩),
        (ggTWSc_refl ha _ _).symm⟩
  | one => exact ⟨1, Submonoid.one_mem _, by rw [mul_one, ggTWSc_mul_inv ha]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨s, hs, rfl⟩ := ihx
    obtain ⟨t, ht, rfl⟩ := ihy
    refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
    calc ggTWSc p N a * s * ggTWSc p N a⁻¹ * (ggTWSc p N a * t * ggTWSc p N a⁻¹)
        = ggTWSc p N a * s * (ggTWSc p N a⁻¹ * ggTWSc p N a) * t * ggTWSc p N a⁻¹ := by
          simp only [mul_assoc]
      _ = ggTWSc p N a * (s * t) * ggTWSc p N a⁻¹ := by
          rw [ggTWSc_inv_mul ha, mul_one]; simp only [mul_assoc]

@[expose] def ggTWScEquiv {a : ZMod p} (ha : a ≠ 0) : GGTWE p N ≃ₗ[ZMod p] GGTWE p N :=
  LinearEquiv.ofLinear (ggTWSc p N a) (ggTWSc p N a⁻¹) (ggTWSc_mul_inv ha) (ggTWSc_inv_mul ha)

theorem ggTWSc_tv {a : ZMod p} (ha : a ≠ 0) {s : Module.End (ZMod p) (GGTWE p N)}
    (h : GGTWIsTv (ggTWSc p N a * s * ggTWSc p N a⁻¹)) : GGTWIsTv s := by
  obtain ⟨hr, hsq⟩ := h
  refine ⟨?_, fun u => ?_⟩
  · have heq : ggTWSc p N a * s * ggTWSc p N a⁻¹ - LinearMap.id =
        (ggTWSc p N a : GGTWE p N →ₗ[ZMod p] GGTWE p N) ∘ₗ
          ((s - LinearMap.id) ∘ₗ (ggTWSc p N a⁻¹ : GGTWE p N →ₗ[ZMod p] GGTWE p N)) := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.comp_apply,
        LinearMap.id_apply, map_sub, ggTWSc_sc_inv ha]
    have hsurj : LinearMap.range (ggTWSc p N a⁻¹ : GGTWE p N →ₗ[ZMod p] GGTWE p N) = ⊤ :=
      LinearMap.range_eq_top.mpr fun v => ⟨ggTWSc p N a v, ggTWSc_inv_sc ha v⟩
    rw [heq, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hsurj] at hr
    have hm := LinearEquiv.finrank_map_eq (ggTWScEquiv (N := N) ha)
      (LinearMap.range (s - LinearMap.id))
    change Module.finrank (ZMod p)
      (Submodule.map (ggTWSc p N a : GGTWE p N →ₗ[ZMod p] GGTWE p N)
        (LinearMap.range (s - LinearMap.id))) = _ at hm
    rw [← hm]
    exact hr
  · have h := hsq (ggTWSc p N a u)
    simp only [Module.End.mul_apply, ggTWSc_inv_sc ha, ← map_sub] at h
    have h' := congrArg (ggTWSc p N a⁻¹) h
    rwa [ggTWSc_inv_sc ha, ggTWSc_inv_sc ha] at h'

theorem ggTWSc_isRefl {a : ZMod p} (ha : a ≠ 0) {s : Module.End (ZMod p) (GGTWE p N)}
    (h : GGTWIsRefl (ggTWSc p N a * s * ggTWSc p N a⁻¹)) : GGTWIsRefl s := by
  obtain ⟨c, f, hcf, heq⟩ := h
  have hs : s = ggTWSc p N a⁻¹ * (ggTWSc p N a * s * ggTWSc p N a⁻¹) * ggTWSc p N a := by
    calc s = (ggTWSc p N a⁻¹ * ggTWSc p N a) * s * (ggTWSc p N a⁻¹ * ggTWSc p N a) := by
          rw [ggTWSc_inv_mul ha, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  have hai : a⁻¹ ≠ 0 := inv_ne_zero ha
  refine ⟨ggTWSc p N a⁻¹ c, ggTWSc p N a f, ?_, ?_⟩
  · rw [ggTWdot_sc, ggTWSc_sc_inv ha, hcf]
  · have hr := ggTWSc_refl hai c f
    rw [inv_inv] at hr
    rw [hs, heq, hr]

theorem ggTWSc_moves {a : ZMod p} (ha : a ≠ 0) {s : Module.End (ZMod p) (GGTWE p N)}
    (h : GGTWMovesLine (ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N))) (ggTWx p N)
      (ggTWSc p N a * s * ggTWSc p N a⁻¹)) :
    GGTWMovesLine (ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N))) (ggTWx p N) s := by
  obtain ⟨hx, v, hv, hmv⟩ := h
  refine ⟨?_, v, hv, fun w hw c d hc heq => hmv w hw c (d * a) hc ?_⟩
  · simp only [Module.End.mul_apply, ggTWSc_x, map_smul] at hx
    have h' := congrArg (ggTWSc p N a⁻¹) hx
    rw [map_smul, ggTWSc_inv_sc ha, ggTWSc_x] at h'
    exact smul_right_injective _ (inv_ne_zero ha) h'
  · simp only [Module.End.mul_apply, ggTWSc_roots a⁻¹ hv, heq, map_add, map_smul,
      ggTWSc_roots a hw, ggTWSc_x, smul_smul]

theorem ggTWKill_frame_sc {a : ZMod p} (ha : a ≠ 0) (pos : GGTWPos)
    (news : Set (GGTWE p N × GGTWE p N)) (y y' : GGTWE p N)
    (h : GGTWKill .frame p N pos (ggTWScNews p N a news) y') :
    GGTWKill .frame p N pos news y := by
  rcases h with ⟨g, hg, htv⟩ | ⟨s', hs', hrefl, hmove⟩
  · obtain ⟨s, hs, rfl⟩ := ggTWSc_closure ha news hg
    exact Or.inl ⟨s, hs, ggTWSc_tv ha htv⟩
  · obtain ⟨s, hs, rfl⟩ := ggTWSc_closure ha news hs'
    exact Or.inr ⟨s, hs, ggTWSc_isRefl ha hrefl, ggTWSc_moves ha hmove⟩

theorem ggTWdot_sc_pair {a : ZMod p} (ha : a ≠ 0) (f v : GGTWE p N) :
    ggTWdot (ggTWSc p N a⁻¹ f) (ggTWSc p N a v) = ggTWdot f v := by
  rw [ggTWdot_sc, ggTWSc_inv_sc ha]

theorem ggTWdot_sc_h (b : ZMod p) (f : GGTWE p N) (i : Fin (N - 1)) :
    ggTWdot (ggTWSc p N b f) (ggTWh p N i) = ggTWdot f (ggTWh p N i) := by
  rw [ggTWdot_sc, ggTWSc_h]

theorem ggTWdot_α_sc (b : ZMod p) (v : GGTWE p N) (i : Fin (N - 1)) :
    ggTWdot (ggTWα p N i) (ggTWSc p N b v) = ggTWdot (ggTWα p N i) v := by
  rw [← ggTWdot_sc, ggTWSc_α]

theorem ggTWdot_sc_x (b : ZMod p) (f : GGTWE p N) :
    ggTWdot (ggTWSc p N b f) (ggTWx p N) = b * ggTWdot f (ggTWx p N) := by
  rw [ggTWdot_sc, ggTWSc_x, ggTWdot_smul_right]

theorem ggTWdot_sc_y {a : ZMod p} (ha : a ≠ 0) (f : GGTWE p N) (pos : GGTWPos) (lam mu : ZMod p) :
    ggTWdot (ggTWSc p N a⁻¹ f) ((a * lam) • ggTWx p N + mu • ggTWz p N pos) =
      ggTWdot f (lam • ggTWx p N + mu • ggTWz p N pos) := by
  rw [ggTWdot_sc, map_add, map_smul, map_smul, ggTWSc_x, ggTWSc_z, smul_smul, mul_comm a lam,
    mul_inv_cancel_right₀ ha]

theorem twlkF_dotX {l : List ℕ} (hl : l.length = N - 1) {k : ℕ} (hk : k < p)
    (h : ggTWdot (ggTWNToZ p N l) (ggTWx p N) = (k : ZMod p)) : ggDepANDot p l (ggTWNX N) = k := by
  rw [← ggTWNX_toZ] at h
  exact twNDot_eq (N := N - 1) hl (ggTWNX_length N) hk h

theorem pat1N_of_cover {RF : List (List ℕ)} {S : List KPat1} {T : List KPat2}
    (hC : kCover N S T = true) (hS : ∀ i < S.length, kPat1NAt p N RF S i = true)
    (posn c0 mi ni : ℕ) (hpos : posn = 0 ∨ posn = 1) (hc0 : c0 < N - 1) (hmi : mi = 1 ∨ mi = 2)
    (hni : ni = 1 ∨ ni = 2) (hpat : ggTWNPat1B N posn c0 mi ni = true) :
    ∃ wits ents, kAll2 (kCell p N posn RF kRTF wits) (kCells1N p N posn c0 mi ni) ents = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c0 (List.mem_range.mpr hc0)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.1 mi (by rcases hmi with rfl | rfl <;> simp)
  have h4 := List.all_eq_true.mp h3 ni (by rcases hni with rfl | rfl <;> simp)
  have h5 : (posn, c0, mi, ni) ∈ S.map (·.1) := by simpa [hpat] using h4
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hS i hi
  simp only [kPat1NAt, List.getElem?_eq_getElem hi] at h6
  have h7 : kPat1N p N RF (S[i].1, S[i].2.1, S[i].2.2) = true := h6
  rw [hek] at h7
  exact ⟨_, _, h7⟩

theorem pat2N_of_cover {RF : List (List ℕ)} {S : List KPat1} {T : List KPat2}
    (hC : kCover N S T = true) (hT : ∀ i < T.length, kPat2NAt p N RF T i = true)
    (posn c : ℕ) (c2 : Option ℕ) (hpos : posn = 0 ∨ posn = 1) (hc : c < N - 1)
    (hc2 : c2 ∈ none :: (List.range (N - 1)).map some)
    (hpat : ggTWNPat2B N posn c c2 = true) :
    ∃ wits ents, kAll2 (kCell p N posn RF kRTF wits) (kCells2N p N posn c c2) ents = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.2 c2 hc2
  have h5 : (posn, c, ggTWNCode c2) ∈ T.map (·.1) := by simpa [hpat] using h3
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hT i hi
  simp only [kPat2NAt, List.getElem?_eq_getElem hi] at h6
  have h7 : kPat2N p N RF (T[i].1, T[i].2.1, T[i].2.2) = true := h6
  rw [hek] at h7
  have h8 : kAll2 (kCell p N posn RF kRTF T[i].2.1)
      (kCells2N p N posn c (kDecode (ggTWNCode c2))) T[i].2.2 = true := h7
  rw [kDecode_code] at h8
  exact ⟨_, _, h8⟩

theorem twlkF_cell (hp : 3 ≤ p) (hN : 5 ≤ N) {RF : List (List ℕ)}
    (hR : kRootsOK p N RF = true) (pos : GGTWPos) (wits : List KKill)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (code : ℕ × ℕ)
    (h : kCell p N (ggTWPosNat pos) RF kRTF wits news code = true) (y : GGTWE p N) :
    GGTWKill .frame p N pos (ggTWNNews p N news) y := by
  obtain ⟨hRF, hR'⟩ := kRoots_eq hR
  unfold kCell at h
  split_ifs at h with h0
  · rw [Bool.and_eq_true, hRF] at h
    exact ggTWNKillTest_sound hp hN hnews hR' _ h.1 h.2 pos y
  · simp [kRTF] at h

theorem twlkF_surv1 (hp : 3 ≤ p) (hN : 5 ≤ N) {RF : List (List ℕ)}
    {S : List KPat1} {T : List KPat2} (hR : kRootsOK p N RF = true)
    (hC : kCover N S T = true) (hS : ∀ i < S.length, kPat1NAt p N RF S i = true) :
    ¬ GGTWSurv1 .frame p N := by
  rintro ⟨pos, c0, m, n, ha, αa, lam, mu, hpat, hpair, hdot, hx, -, -, hkf⟩
  obtain ⟨mi, ni, hmi, hni, rfl, rfl⟩ := twPat1_wit hpat
  have hpatB := (ggTWNPat1B_iff pos c0.val mi ni hmi hni).mpr hpat
  obtain ⟨wits, ents, hchk⟩ := pat1N_of_cover hC hS (ggTWPosNat pos) c0.val mi ni
    (twPosNat_mem pos) c0.isLt hmi hni hpatB
  set a := ggTWdot αa (ggTWx p N) with ha_def
  have ha0 : a ≠ 0 := hx
  have hpair' : GGTWPairs1 p N pos c0 (-(mi : ℤ)) (-(ni : ℤ)) (ggTWSc p N a ha)
      (ggTWSc p N a⁻¹ αa) := by
    intro c hc
    rw [ggTWdot_sc_h, ggTWdot_α_sc]
    exact hpair c hc
  have hdot' : ggTWdot (ggTWSc p N a⁻¹ αa) (ggTWSc p N a ha) = 2 := by
    rw [ggTWdot_sc_pair ha0, hdot]
  have hx1 : ggTWdot (ggTWSc p N a⁻¹ αa) (ggTWx p N) = 1 := by
    rw [ggTWdot_sc_x, ← ha_def, inv_mul_cancel₀ ha0]
  obtain ⟨lh, la, hlh, hla, hd, -, hvp, hnews⟩ :=
    ggTWLEnc1 hp hN pos c0 mi ni hmi hni _ _ hpair' hdot' (by rw [hx1]; exact one_ne_zero)
  have hla_eq : ggTWNToZ p N la = ggTWSc p N a⁻¹ αa := by
    have hm : (ggTWNToZ p N lh, ggTWNToZ p N la) ∈ ggTWNNews p N [(lh, la)] :=
      ⟨(lh, la), by simp, rfl⟩
    rw [hnews, Set.mem_singleton_iff] at hm
    exact congrArg Prod.snd hm
  have hlaX : ggDepANDot p la (ggTWNX N) = 1 :=
    twlkF_dotX hvp.2.1 (by omega) (by rw [hla_eq, hx1, Nat.cast_one])
  have hmem : [(lh, la)] ∈ kCells1N p N (ggTWPosNat pos) c0.val mi ni := by
    simp only [kCells1N, List.mem_flatMap, List.mem_filterMap]
    refine ⟨lh, kSolH_complete hN pos _ hlh, la, ?_, by simp [hd]⟩
    exact List.mem_filter.mpr ⟨kSolA_complete hN pos _ hla, by simp [hlaX]⟩
  obtain ⟨code, hcode⟩ := twlk_all2_mem _ _ ents hchk _ hmem
  have hvalid : ∀ q ∈ [(lh, la)], GGTWNValid p N q := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hvp
  have hk := twlkF_cell hp hN hR pos wits hvalid code hcode (ggTWx p N)
  have himg : ggTWScNews p N a {(ha, αa)} = {(ggTWSc p N a ha, ggTWSc p N a⁻¹ αa)} :=
    Set.image_singleton
  rw [hnews, ← himg] at hk
  exact hkf (ggTWKill_frame_sc ha0 pos _ _ _ hk)

theorem twlkF_surv2 (hp : 3 ≤ p) (hN : 5 ≤ N) {RF : List (List ℕ)}
    {S : List KPat1} {T : List KPat2} (hR : kRootsOK p N RF = true)
    (hC : kCover N S T = true) (hT : ∀ i < T.length, kPat2NAt p N RF T i = true) :
    ¬ GGTWSurv2 .frame p N := by
  rintro ⟨pos, c, c₂, ha1, αa1, ha2, αa2, lam, mu, hpat, hpair, hx, hlm, h1, h2, hkf⟩
  have hpatB := (ggTWNPat2B_iff pos c.val (c₂.map Fin.val)).mpr hpat
  have hc2m : c₂.map Fin.val ∈ none :: (List.range (N - 1)).map some := by
    cases c₂ with
    | none => simp
    | some c' =>
        exact List.mem_cons_of_mem none
          (List.mem_map.mpr ⟨c'.val, List.mem_range.mpr c'.isLt, rfl⟩)
  obtain ⟨wits, ents, hchk⟩ := pat2N_of_cover hC hT (ggTWPosNat pos) c.val (c₂.map Fin.val)
    (twPosNat_mem pos) c.isLt hc2m hpatB
  set e1 := ggTWdot αa1 (ggTWx p N) with he1d
  set e2 := ggTWdot αa2 (ggTWx p N) with he2d
  set a := if e2 ≠ 0 then e2 else e1 with ha_def
  have ha0 : a ≠ 0 := by
    rw [ha_def]
    split_ifs with h
    · exact h
    · rcases hx with h' | h'
      · exact h'
      · exact absurd h' h
  have hpair' : GGTWPairs2 p N pos c c₂ (ggTWSc p N a ha1) (ggTWSc p N a⁻¹ αa1)
      (ggTWSc p N a ha2) (ggTWSc p N a⁻¹ αa2) := by
    obtain ⟨hP, hP1, hP2, hP3, hP4⟩ := hpair
    refine ⟨fun c' hc' => ?_, ?_, ?_, ?_, ?_⟩
    · rw [ggTWdot_sc_h, ggTWdot_α_sc, ggTWdot_sc_h, ggTWdot_α_sc]
      exact hP c' hc'
    · rw [ggTWdot_sc_pair ha0, hP1]
    · rw [ggTWdot_sc_pair ha0, hP2]
    · rw [ggTWdot_sc_pair ha0, hP3]
    · rw [ggTWdot_sc_pair ha0, hP4]
  have hx1' : ggTWdot (ggTWSc p N a⁻¹ αa1) (ggTWx p N) = a⁻¹ * e1 := ggTWdot_sc_x _ _
  have hx2' : ggTWdot (ggTWSc p N a⁻¹ αa2) (ggTWx p N) = a⁻¹ * e2 := ggTWdot_sc_x _ _
  have hx' : ggTWdot (ggTWSc p N a⁻¹ αa1) (ggTWx p N) ≠ 0 ∨
      ggTWdot (ggTWSc p N a⁻¹ αa2) (ggTWx p N) ≠ 0 := by
    rw [hx1', hx2']
    rcases hx with h | h
    · exact Or.inl (mul_ne_zero (inv_ne_zero ha0) h)
    · exact Or.inr (mul_ne_zero (inv_ne_zero ha0) h)
  have hlm' : a * lam ≠ 0 ∨ mu ≠ 0 := by
    rcases hlm with h | h
    · exact Or.inl (mul_ne_zero ha0 h)
    · exact Or.inr h
  obtain ⟨lh1, la1, lh2, la2, hlh1, hla1, hlh2, hla2, hd1, hd2, hd3, hd4, -, hdet,
    hvp1, hvp2, hnews⟩ := ggTWLEnc2 hp hN pos c c₂ _ _ _ _ hpair' hx' (a * lam) mu hlm'
      (by rw [ggTWdot_sc_y ha0]; exact h1) (by rw [ggTWdot_sc_y ha0]; exact h2)
  have hc2c : c₂ ≠ some c := by
    rintro rfl
    obtain ⟨-, -, -, hpl⟩ := hpat
    rcases hpl with ⟨h0, h1'⟩ | ⟨h0, h1'⟩ <;> omega
  have hne1 : ggTWNToZ p N la1 ≠ ggTWSc p N a⁻¹ αa2 := by
    intro heq
    have hcJ : ggTWInJ N pos c.val := hpat.1
    have hs := (ggTWNSolA_sound hla1).2 c hcJ
    have hq := (hpair'.1 c hcJ).2.2.1
    rw [if_neg (fun h => hc2c h.symm)] at hq
    have hm1 : ((if c.val = c.val then (p - 1) % p else 0 : ℕ) : ZMod p) = -1 := by
      rw [if_pos rfl, twCast_neg_one]
    rw [heq, hq] at hs
    exact neg_ne_zero.mpr one_ne_zero (hs.trans hm1).symm
  have hmem2 : ggTWNToZ p N la1 = ggTWSc p N a⁻¹ αa1 ∧ ggTWNToZ p N la2 = ggTWSc p N a⁻¹ αa2 := by
    have hm1 : (ggTWNToZ p N lh1, ggTWNToZ p N la1) ∈ ggTWNNews p N [(lh1, la1), (lh2, la2)] :=
      ⟨(lh1, la1), by simp, rfl⟩
    have hm2 : (ggTWSc p N a ha2, ggTWSc p N a⁻¹ αa2) ∈ ggTWNNews p N [(lh1, la1), (lh2, la2)] := by
      rw [hnews]
      exact Set.mem_insert_of_mem _ rfl
    rw [hnews, Set.mem_insert_iff, Set.mem_singleton_iff] at hm1
    refine ⟨?_, ?_⟩
    · rcases hm1 with hm1 | hm1
      · exact congrArg Prod.snd hm1
      · exact absurd (congrArg Prod.snd hm1) hne1
    · obtain ⟨q, hq, hqe⟩ := hm2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact absurd (congrArg Prod.snd hqe).symm hne1
      · exact (congrArg Prod.snd hqe).symm
  have hA2 : la2 ∈ kSolAX p N (ggTWPosNat pos) (ggTWNTgt2 p (c₂.map Fin.val)) 1 ++
      (if ggDepANDot p la1 (ggTWNX N) == 1 then
        kSolAX p N (ggTWPosNat pos) (ggTWNTgt2 p (c₂.map Fin.val)) 0 else []) := by
    have A2 := kSolA_complete hN pos _ hla2
    by_cases he2 : e2 ≠ 0
    · have hai : a = e2 := by rw [ha_def, if_pos he2]
      have h2X : ggDepANDot p la2 (ggTWNX N) = 1 :=
        twlkF_dotX hvp2.2.1 (by omega)
          (by rw [hmem2.2, hx2', hai, inv_mul_cancel₀ he2, Nat.cast_one])
      exact List.mem_append_left _ (List.mem_filter.mpr ⟨A2, by simp [h2X]⟩)
    · have he2' : e2 = 0 := not_not.mp he2
      have hai : a = e1 := by rw [ha_def, if_neg he2]
      have he1 : e1 ≠ 0 := by rw [← hai]; exact ha0
      have h1X : ggDepANDot p la1 (ggTWNX N) = 1 :=
        twlkF_dotX hvp1.2.1 (by omega)
          (by rw [hmem2.1, hx1', hai, inv_mul_cancel₀ he1, Nat.cast_one])
      have h2X : ggDepANDot p la2 (ggTWNX N) = 0 :=
        twlkF_dotX hvp2.2.1 (Fact.out : p.Prime).pos
          (by rw [hmem2.2, hx2', he2', mul_zero, Nat.cast_zero])
      refine List.mem_append_right _ ?_
      rw [h1X, beq_self_eq_true, if_pos rfl]
      exact List.mem_filter.mpr ⟨A2, by simp [h2X]⟩
  have ht1 : kTgt1 p c.val 1 = fun c' => if c' = c.val then (p - 1) % p else 0 := by
    funext c'
    simp [kTgt1, Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hmem : [(lh1, la1), (lh2, la2)] ∈
      kCells2N p N (ggTWPosNat pos) c.val (c₂.map Fin.val) := by
    have H1 := kSolH_complete hN pos _ hlh1
    have A1 := kSolA_complete hN pos _ hla1
    have H2 := kSolH_complete hN pos _ hlh2
    rw [← ht1] at H1 A1
    cases c₂ with
    | none =>
      simp only [Option.map_none] at H2 hA2 hd2 hd4 ⊢
      simp only [kCells2N, List.mem_flatMap, List.mem_filterMap]
      refine ⟨lh1, H1, la1, A1, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd1), List.mem_flatMap]
      refine ⟨lh2, H2, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd2), List.mem_filterMap]
      exact ⟨la2, hA2, by simp [hd3, hd4, hdet]⟩
    | some c' =>
      simp only [Option.map_some] at H2 hA2 hd2 hd4 ⊢
      simp only [kCells2N, List.mem_flatMap, List.mem_filterMap]
      refine ⟨lh1, H1, la1, A1, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd1), List.mem_flatMap]
      refine ⟨lh2, H2, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd2), List.mem_filterMap]
      exact ⟨la2, hA2, by simp [hd3, hd4, hdet]⟩
  obtain ⟨code, hcode⟩ := twlk_all2_mem _ _ ents hchk _ hmem
  have hvalid : ∀ q ∈ [(lh1, la1), (lh2, la2)], GGTWNValid p N q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hvp1
    · exact hvp2
  have hk := twlkF_cell hp hN hR pos wits hvalid code hcode (ggTWx p N)
  have himg : ggTWScNews p N a {(ha1, αa1), (ha2, αa2)} =
      {(ggTWSc p N a ha1, ggTWSc p N a⁻¹ αa1), (ggTWSc p N a ha2, ggTWSc p N a⁻¹ αa2)} :=
    Set.image_pair _ _ _
  rw [hnews, ← himg] at hk
  exact hkf (ggTWKill_frame_sc ha0 pos _ _ _ hk)

theorem twlkF_sound (hp : 3 ≤ p) (hN : 5 ≤ N) (RF : List (List ℕ))
    (S : List KPat1) (T : List KPat2) (hR : kRootsOK p N RF = true)
    (hC : kCover N S T = true) (hS : ∀ i < S.length, kPat1NAt p N RF S i = true)
    (hT : ∀ i < T.length, kPat2NAt p N RF T i = true) : GGTWCells .frame p N :=
  ⟨twlkF_surv1 hp hN hR hC hS, twlkF_surv2 hp hN hR hC hT⟩

end CFSG.StandardType.TWLKF

end

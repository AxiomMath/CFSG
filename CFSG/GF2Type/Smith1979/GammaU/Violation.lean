
module

public import CFSG.GF2Type.Smith1979.GammaU.ViolationDefs
public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.GF2Type.Smith1979.GammaU.Viol

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] def GenSet (gs : List (Array ℕ)) : Set (V12 ≃ₗ[ZMod 2] V12) :=
  {l | ∃ r ∈ gs, ∀ x, l x = linOfRows r x}

@[expose] def genGrp (gs : List (Array ℕ)) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  Subgroup.closure (GenSet gs)

@[expose] def InFrame (Lc : List (Array ℕ)) (u : V12 ≃ₗ[ZMod 2] V12) (r : Array ℕ) : Prop :=
  ∃ r' ∈ Lc, ∀ x, u⁻¹ (linOfRows r (u x)) = linOfRows r' x

@[expose] def F4Indep (x y : V12) : Prop := x ≠ 0 ∧ ∀ a b : ZMod 2, y ≠ a • x + b • theta0 x

@[expose] def F2Indep3 (x y w : V12) : Prop :=
  ∀ a b c : ZMod 2, a • x + b • y + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0

@[expose] def Violation (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (Lc H : List (Array ℕ)) : Prop :=
  (∃ h ∈ N, h (vecOf a0) = vecOf a0 ∧
      ∃ r ∈ Lc, ¬ ∃ r' ∈ Lc, ∀ x, h (linOfRows r (h⁻¹ x)) = linOfRows r' x) ∨
    (∃ r ∈ Lc, (∀ x, linOfRows r (theta0 x) = theta0 (linOfRows r x)) ∧ r ∉ H ∧
      ∃ u₁ ∈ N, ∃ u₂ ∈ N, InFrame Lc u₁ r ∧ InFrame Lc u₂ r ∧
        F4Indep (u₁ (vecOf a0)) (u₂ (vecOf a0))) ∨
    (∃ r ∈ Lc, (∀ x, linOfRows r (theta0 x) = theta0 (theta0 (linOfRows r x))) ∧
      ∃ u₁ ∈ N, ∃ u₂ ∈ N, ∃ u₃ ∈ N, InFrame Lc u₁ r ∧ InFrame Lc u₂ r ∧ InFrame Lc u₃ r ∧
        F2Indep3 (u₁ (vecOf a0)) (u₂ (vecOf a0)) (u₃ (vecOf a0)))

theorem okRows_spec {r : Array ℕ} (h : okRows r = true) : r.size = 12 ∧ ∀ x ∈ r, x < 4096 := by
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  exact ⟨h.1, fun x hx => by simpa using h.2 x hx⟩

theorem not_mem_of_contains {l : List (Array ℕ)} {a : Array ℕ} (h : l.contains a = false) :
    a ∉ l := fun hm => by
  rw [List.contains_iff_mem.2 hm] at h
  exact Bool.noConfusion h

theorem size_mulR (g h : Array ℕ) : (mulR g h).size = h.size := by
  simp [mulR]

theorem lt_of_mem_mulR {g h : Array ℕ} (hg : ∀ x ∈ g, x < 4096) : ∀ x ∈ mulR g h, x < 4096 := by
  intro x hx
  simp only [mulR, Array.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact appN_lt hg y

theorem okRows_mulR {g h : Array ℕ} (hg : okRows g = true) (hh : okRows h = true) :
    okRows (mulR g h) = true := by
  have hg' := okRows_spec hg
  have hh' := okRows_spec hh
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq]
  exact ⟨by rw [size_mulR, hh'.1], fun x hx => lt_of_mem_mulR hg'.2 x hx⟩

@[expose] noncomputable def eqvOf (g gi : Array ℕ) (h1 : mulR g gi = idR) (h2 : mulR gi g = idR) :
    V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofLinear (linOfRows g) (linOfRows gi)
    (LinearMap.ext fun x => by
      change linOfRows g (linOfRows gi x) = x
      rw [← linOfRows_mulR, h1, linOfRows_idR])
    (LinearMap.ext fun x => by
      change linOfRows gi (linOfRows g x) = x
      rw [← linOfRows_mulR, h2, linOfRows_idR])

theorem eqvOf_apply (g gi : Array ℕ) (h1 : mulR g gi = idR) (h2 : mulR gi g = idR) (x : V12) :
    eqvOf g gi h1 h2 x = linOfRows g x := rfl

theorem eqvOf_inv_apply (g gi : Array ℕ) (h1 : mulR g gi = idR) (h2 : mulR gi g = idR)
    (x : V12) : (eqvOf g gi h1 h2)⁻¹ x = linOfRows gi x := rfl

@[expose] def StInv (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (s : St) : Prop :=
  okRows s.2.1 = true ∧ okRows s.2.2 = true ∧
    ∃ U ∈ N, (∀ x, U x = linOfRows s.2.1 x) ∧ ∀ x, U⁻¹ x = linOfRows s.2.2 x

@[expose] def GensOK (gs : List (Array ℕ)) : Prop :=
  ∀ g ∈ gs, okRows g = true ∧ okRows (invR g) = true ∧ mulR g (invR g) = idR ∧
    mulR (invR g) g = idR

theorem gen_mem {gs : List (Array ℕ)} (hgs : GensOK gs) {g : Array ℕ} (hg : g ∈ gs) :
    eqvOf g (invR g) (hgs g hg).2.2.1 (hgs g hg).2.2.2 ∈ genGrp gs :=
  Subgroup.subset_closure ⟨g, hg, fun _ => rfl⟩

theorem mem_withInv {gs : List (Array ℕ)} {p : Array ℕ × Array ℕ} (hp : p ∈ withInv gs) :
    ∃ g ∈ gs, p = (g, invR g) := by
  simp only [withInv, List.mem_map] at hp
  obtain ⟨g, hg, rfl⟩ := hp
  exact ⟨g, hg, rfl⟩

@[expose] def PairsOK (W : List (Array ℕ × Array ℕ)) : Prop :=
  ∀ p ∈ W, okRows p.1 = true ∧ okRows p.2 = true ∧ mulR p.1 p.2 = idR ∧ mulR p.2 p.1 = idR

theorem pairsOK_withInv {gs : List (Array ℕ)} (hgs : GensOK gs) : PairsOK (withInv gs) := by
  intro p hp
  obtain ⟨g, hg, rfl⟩ := mem_withInv hp
  exact hgs g hg

theorem map_fst_withInv (gs : List (Array ℕ)) : (withInv gs).map Prod.fst = gs := by
  simp only [withInv, List.map_map]
  exact List.map_id' gs

theorem genW_mem {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) {p : Array ℕ × Array ℕ}
    (hp : p ∈ W) : eqvOf p.1 p.2 (hW p hp).2.2.1 (hW p hp).2.2.2 ∈ genGrp (W.map Prod.fst) :=
  Subgroup.subset_closure ⟨p.1, List.mem_map.2 ⟨p, hp, rfl⟩, fun _ => rfl⟩

theorem stepOf_inv {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) {p : Array ℕ × Array ℕ}
    (hp : p ∈ W) (s : St) (hs : StInv (genGrp (W.map Prod.fst)) s) :
    StInv (genGrp (W.map Prod.fst)) (stepOf p s) := by
  obtain ⟨hok, hiok, U, hU, hUx, hUi⟩ := hs
  obtain ⟨hgok, hgiok, h1, h2⟩ := hW p hp
  refine ⟨okRows_mulR hgok hok, okRows_mulR hiok hgiok, eqvOf p.1 p.2 h1 h2 * U,
    mul_mem (genW_mem hW hp) hU, fun x => ?_, fun x => ?_⟩
  · rw [LinearEquiv.mul_apply, hUx, eqvOf_apply]
    exact (linOfRows_mulR p.1 s.2.1 x).symm
  · rw [mul_inv_rev, LinearEquiv.mul_apply, hUi, eqvOf_inv_apply]
    exact (linOfRows_mulR s.2.2 p.2 x).symm

theorem orbitTr_spec {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) :
    ∀ s ∈ orbitTr W, StInv (genGrp (W.map Prod.fst)) s := by
  unfold orbitTr
  refine bfsClosure_inv _ _ ?_ _ _ _ _ ?_ (by simp)
  · intro f hf s hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hf
    exact stepOf_inv hW hp s hs
  · simp only [List.mem_singleton, forall_eq]
    have hid : okRows idR = true := by simp [okRows, idR]
    exact ⟨hid, hid, 1, one_mem _, fun x => (linOfRows_idR x).symm,
      fun x => (linOfRows_idR x).symm⟩

theorem d1Check_spec {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) {Lc Lg : List (Array ℕ)}
    (hLc : ∀ r ∈ Lc, okRows r = true) (hLg : ∀ r ∈ Lg, r ∈ Lc)
    (h : d1Check W (orbitTr W) Lc Lg = true) :
    ∃ h ∈ genGrp (W.map Prod.fst), h (vecOf a0) = vecOf a0 ∧
      ∃ r ∈ Lc, ¬ ∃ r' ∈ Lc, ∀ x, h (linOfRows r (h⁻¹ x)) = linOfRows r' x := by
  simp only [d1Check, List.any_eq_true] at h
  obtain ⟨s, hs, p, hp, hfind⟩ := h
  split at hfind
  · exact absurd hfind (by simp)
  rename_i t ht
  have htO := List.mem_of_find?_eq_some ht
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true'] at hfind
  obtain ⟨hfix, l, hl, hnot⟩ := hfind
  obtain ⟨hsok, hsiok, S, hS, hSx, hSi⟩ := orbitTr_spec hW s hs
  obtain ⟨htok, htiok, T, hT, hTx, hTi⟩ := orbitTr_spec hW t htO
  obtain ⟨hgok, hgiok, h1, h2⟩ := hW p hp
  set P := eqvOf p.1 p.2 h1 h2
  have hH : ∀ x, (T⁻¹ * P * S) x = linOfRows (mulR t.2.2 (mulR p.1 s.2.1)) x := fun x => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hSx, eqvOf_apply, hTi, linOfRows_mulR,
      linOfRows_mulR]
  have hHi : ∀ x, (T⁻¹ * P * S)⁻¹ x = linOfRows (mulR s.2.2 (mulR p.2 t.2.1)) x := fun x => by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTx,
      eqvOf_inv_apply, hSi, linOfRows_mulR, linOfRows_mulR]
  refine ⟨T⁻¹ * P * S, mul_mem (mul_mem (inv_mem hT) (genW_mem hW hp)) hS, ?_, l, hLg l hl, ?_⟩
  · rw [hH, ← vecOf_appN, hfix]
  · rintro ⟨r', hr', hr'x⟩
    apply not_mem_of_contains hnot
    have hhok : okRows (mulR t.2.2 (mulR p.1 s.2.1)) = true :=
      okRows_mulR htiok (okRows_mulR hgok hsok)
    have hhiok : okRows (mulR s.2.2 (mulR p.2 t.2.1)) = true :=
      okRows_mulR hsiok (okRows_mulR hgiok htok)
    have hcok := okRows_mulR hhok (okRows_mulR (hLc l (hLg l hl)) hhiok)
    have heq := rows_eq (okRows_spec hcok).1 (okRows_spec (hLc r' hr')).1 (okRows_spec hcok).2
      (okRows_spec (hLc r' hr')).2 fun x => by
        rw [linOfRows_mulR (mulR t.2.2 (mulR p.1 s.2.1)), linOfRows_mulR l, ← hH, ← hHi, hr'x]
    rw [heq]
    exact hr'

theorem mem_ptsOf {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) {Lc : List (Array ℕ)}
    {s : Array ℕ} {x : ℕ} (hx : x ∈ ptsOf (orbitTr W) Lc s) :
    x < 4096 ∧ ∃ U ∈ genGrp (W.map Prod.fst), InFrame Lc U s ∧ U (vecOf a0) = vecOf x := by
  simp only [ptsOf, List.mem_filterMap] at hx
  obtain ⟨t, ht, hx⟩ := hx
  split at hx
  · rename_i hc
    obtain ⟨htok, htiok, T, hT, hTx, hTi⟩ := orbitTr_spec hW t ht
    simp only [Option.some.injEq] at hx
    subst hx
    refine ⟨appN_lt (okRows_spec htok).2 _, T, hT,
      ⟨_, List.contains_iff_mem.1 hc, fun z => ?_⟩, ?_⟩
    · rw [hTx, hTi, linOfRows_mulR, linOfRows_mulR]
    · rw [hTx, vecOf_appN]
  · exact absurd hx (by simp)

theorem f4Indep_spec {x y : ℕ} (hx : x < 4096) (hy : y < 4096) (h : f4Indep x y = true) :
    F4Indep (vecOf x) (vecOf y) := by
  simp only [f4Indep, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hx0, hy0⟩, hyx⟩, hyt⟩, hyxt⟩ := h
  have htx := theta0N_lt hx
  refine ⟨fun h0 => hx0 ((vecOf_eq_zero hx).1 h0), fun a b hab => ?_⟩
  have ha : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rw [← vecOf_theta0N hx] at hab
  rcases ha a with rfl | rfl <;> rcases ha b with rfl | rfl
  · simp only [zero_smul, add_zero] at hab
    exact hy0 ((vecOf_eq_zero hy).1 hab)
  · simp only [zero_smul, one_smul, zero_add] at hab
    exact hyt (vecOf_inj hy htx hab)
  · simp only [zero_smul, one_smul, add_zero] at hab
    exact hyx (vecOf_inj hy hx hab)
  · simp only [one_smul] at hab
    rw [← vecOf_xor] at hab
    exact hyxt (vecOf_inj hy (xor_lt hx htx) hab)

theorem eq_of_add_eq_zero {x y : V12} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simp only [add_assoc, zero_add] at this
  rwa [show y + y = 0 from funext fun j => by
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize y j = c
    revert c
    decide, add_zero] at this

theorem f2Indep3_spec {x y w : ℕ} (hx : x < 4096) (hy : y < 4096) (hw : w < 4096)
    (h : f2Indep3 x y w = true) : F2Indep3 (vecOf x) (vecOf y) (vecOf w) := by
  simp only [f2Indep3, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hx0, hy0⟩, hyx⟩, hw0⟩, hwx⟩, hwy⟩, hwxy⟩ := h
  have ha : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  intro a b c habc
  have nz : ∀ {n}, n < 4096 → n ≠ 0 → vecOf n ≠ 0 := fun hn hn0 h0 => hn0 ((vecOf_eq_zero hn).1 h0)
  rcases ha a with rfl | rfl <;> rcases ha b with rfl | rfl <;> rcases ha c with rfl | rfl <;>
    simp only [zero_smul, one_smul, add_zero, zero_add, true_and, and_true] at habc ⊢
  · exact (nz hw hw0 habc).elim
  · exact (nz hy hy0 habc).elim
  · exact (hwy (vecOf_inj hw hy (eq_of_add_eq_zero habc).symm)).elim
  · exact (nz hx hx0 habc).elim
  · exact (hwx (vecOf_inj hw hx (eq_of_add_eq_zero habc).symm)).elim
  · exact (hyx (vecOf_inj hy hx (eq_of_add_eq_zero habc).symm)).elim
  · rw [← vecOf_xor] at habc
    exact (hwxy (vecOf_inj hw (xor_lt hx hy) (eq_of_add_eq_zero habc).symm)).elim

theorem d2uCheck_spec {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) {Lc H : List (Array ℕ)}
    (hLc : ∀ r ∈ Lc, okRows r = true) (h : d2uCheck (orbitTr W) Lc H = true) :
    ∃ r ∈ Lc, (∀ x, linOfRows r (theta0 x) = theta0 (linOfRows r x)) ∧ r ∉ H ∧
      ∃ u₁ ∈ genGrp (W.map Prod.fst), ∃ u₂ ∈ genGrp (W.map Prod.fst), InFrame Lc u₁ r ∧ InFrame Lc u₂ r ∧
        F4Indep (u₁ (vecOf a0)) (u₂ (vecOf a0)) := by
  simp only [d2uCheck, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨r, hr, ⟨⟨hu, hH⟩, x, hx, y, hy, hxy⟩⟩ := h
  obtain ⟨hxl, U₁, hU₁, hF₁, hx₁⟩ := mem_ptsOf hW hx
  obtain ⟨hyl, U₂, hU₂, hF₂, hy₂⟩ := mem_ptsOf hW hy
  refine ⟨r, hr, unitary_spec (okRows_spec (hLc r hr)).2 hu, not_mem_of_contains hH, U₁, hU₁, U₂, hU₂, hF₁, hF₂, ?_⟩
  rw [hx₁, hy₂]
  exact f4Indep_spec hxl hyl hxy

theorem d2aCheck_spec {W : List (Array ℕ × Array ℕ)} (hW : PairsOK W) {Lc : List (Array ℕ)}
    (hLc : ∀ r ∈ Lc, okRows r = true) (h : d2aCheck (orbitTr W) Lc = true) :
    ∃ r ∈ Lc, (∀ x, linOfRows r (theta0 x) = theta0 (theta0 (linOfRows r x))) ∧
      ∃ u₁ ∈ genGrp (W.map Prod.fst), ∃ u₂ ∈ genGrp (W.map Prod.fst),
        ∃ u₃ ∈ genGrp (W.map Prod.fst), InFrame Lc u₁ r ∧
        InFrame Lc u₂ r ∧ InFrame Lc u₃ r ∧
          F2Indep3 (u₁ (vecOf a0)) (u₂ (vecOf a0)) (u₃ (vecOf a0)) := by
  simp only [d2aCheck, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨r, hr, ha, x, hx, y, hy, w, hw, hxyw⟩ := h
  obtain ⟨hxl, U₁, hU₁, hF₁, hx₁⟩ := mem_ptsOf hW hx
  obtain ⟨hyl, U₂, hU₂, hF₂, hy₂⟩ := mem_ptsOf hW hy
  obtain ⟨hwl, U₃, hU₃, hF₃, hw₃⟩ := mem_ptsOf hW hw
  refine ⟨r, hr, anti_spec (okRows_spec (hLc r hr)).2 ha, U₁, hU₁, U₂, hU₂, U₃, hU₃, hF₁, hF₂,
    hF₃, ?_⟩
  rw [hx₁, hy₂, hw₃]
  exact f2Indep3_spec hxl hyl hwl hxyw

theorem violCheckW_spec {W : List (Array ℕ × Array ℕ)} {Lc Lg H : List (Array ℕ)} {b : Bool}
    (h : violCheckW W Lc Lg H b = true) : Violation (genGrp (W.map Prod.fst)) Lc H := by
  simp only [violCheckW, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨hW, hLc⟩, hLg⟩, hv⟩ := h
  have hW' : PairsOK W := fun p hp => by
    have := hW p hp
    simp only [pairOK, Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    exact ⟨h1, h2, h3, h4⟩
  have k1 := d1Check_spec hW' hLc hLg
  have k2 := d2uCheck_spec (H := H) hW' hLc
  have k3 := d2aCheck_spec hW' hLc
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hv
  · rcases hv with (hv | hv) | hv
    · exact Or.inr (Or.inl (k2 hv))
    · exact Or.inr (Or.inr (k3 hv))
    · exact Or.inl (k1 hv)
  · rcases hv with (hv | hv) | hv
    · exact Or.inl (k1 hv)
    · exact Or.inr (Or.inl (k2 hv))
    · exact Or.inr (Or.inr (k3 hv))

theorem violCheck_spec {gs Lc Lg H : List (Array ℕ)} (h : violCheck gs Lc Lg H = true) :
    Violation (genGrp gs) Lc H := by
  have := violCheckW_spec h
  rwa [map_fst_withInv] at this

end CFSG.GF2Type.Smith1979.GammaU.Viol

module

public import CFSG.Certificates.Kernel.TwistDce.Core

public section

namespace CFSG.Certificates.TwDce.Core

open CFSG.KC.TwDce CFSG.KC.YModel CFSG.Certificates.CosetEnumeration CFSG.Certificates.TwDce.Words

variable {G : Type*} [Group G]

@[expose] noncomputable def pv (x : ℕ → G) (u : G) (E rot p : ℕ) : G :=
  if (p + rot) % 2 = 0 then x E else u

section Walk

variable {F RD RW RA : ℕ → ℕ} {THM E BS NB : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}

theorem stepRun_mk (r s a : ℕ) : stepRun F THM BS NB RD RW RA r (s, a) =
    if Nat.beq (wsFail s) 1 = true then wsBad a
    else stepCore F THM BS NB RD RW RA r (wsK s) a (wsJ s) := by
  rw [← brec_eq]; rfl

theorem stepRun_fail (r : ℕ) {st : WS} (h : wsFail st.1 = 1) :
    wsFail (stepRun F THM BS NB RD RW RA r st).1 = 1 := by
  obtain ⟨s, a⟩ := st
  rw [stepRun_mk, if_pos (by simpa using h)]
  exact wsBad_fail a

theorem walkStep_mk (r rot pos s a : ℕ) : walkStep F THM E BS NB RD RW RA r rot pos (s, a) =
    if (pos + rot) % 2 = 0 then (s, wCat a (wOne E))
    else stepRun F THM BS NB RD RW RA r (s, a) := by
  have e : walkStep F THM E BS NB RD RW RA r rot pos (s, a) =
      if Nat.beq (Nat.land (pos + rot) 1) 0 = true then (s, wCat a (wOne E))
      else stepRun F THM BS NB RD RW RA r (s, a) := by
    rw [← brec_eq]; rfl
  rw [e]
  have : Nat.land (pos + rot) 1 = (pos + rot) % 2 := Nat.and_one_is_mod _
  simp only [this, Nat.beq_eq]

theorem walkStep_fail (r rot pos : ℕ) {st : WS} (h : wsFail st.1 = 1) :
    wsFail (walkStep F THM E BS NB RD RW RA r rot pos st).1 = 1 := by
  obtain ⟨s, a⟩ := st
  rw [walkStep_mk]
  split_ifs
  · exact h
  · exact stepRun_fail r h

theorem foldl_fail (r rot : ℕ) (ps : List ℕ) : ∀ {st : WS}, wsFail st.1 = 1 →
    wsFail (ps.foldl (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st).1 = 1 := by
  induction ps with
  | nil => exact fun h => h
  | cons p ps ih => exact fun h => ih (walkStep_fail r rot p h)

variable (F THM BS NB RD RW RA H x u) in
theorem stepRun_spec (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r : ℕ} (hH : Hist RD RW RA H x u X r) {st : WS} (ha : GW (2 ^ 22) st.2)
    (hf : wsFail (stepRun F THM BS NB RD RW RA r st).1 = 0) :
    CE H (X (wsK st.1) * val x st.2 * u) (X (wsK (stepRun F THM BS NB RD RW RA r st).1) *
      val x (stepRun F THM BS NB RD RW RA r st).2) ∧
    GW (2 ^ 21) (stepRun F THM BS NB RD RW RA r st).2 := by
  obtain ⟨s, a⟩ := st
  rw [stepRun_mk] at hf ⊢
  split_ifs at hf ⊢ with h
  · exact absurd hf (by rw [wsBad_fail]; norm_num)
  · exact step_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH ha hf

variable (F THM E BS NB RD RW RA H x u) in
theorem walkStep_spec (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1) (hE : E < 10)
    {X : ℕ → G} {r rot pos B : ℕ} (hH : Hist RD RW RA H x u X r) {st : WS}
    (hB1 : 2 ^ 21 ≤ B) (hB2 : B < 2 ^ 22) (ha : GW B st.2)
    (hf : wsFail (walkStep F THM E BS NB RD RW RA r rot pos st).1 = 0) :
    CE H (X (wsK st.1) * val x st.2 * pv x u E rot pos)
      (X (wsK (walkStep F THM E BS NB RD RW RA r rot pos st).1) *
        val x (walkStep F THM E BS NB RD RW RA r rot pos st).2) ∧
    GW (B + 2) (walkStep F THM E BS NB RD RW RA r rot pos st).2 := by
  obtain ⟨s, a⟩ := st
  rw [walkStep_mk] at hf ⊢
  unfold pv
  split_ifs at hf ⊢ with h
  · obtain ⟨o1, o2, o3⟩ := wOne_spec (c := E) (by omega)
    have hO : GW 2 (wOne E) := ⟨o2, by rw [o3]; simpa using hE, by omega⟩
    obtain ⟨g, e⟩ := GW.cat ha hO (by omega)
    refine ⟨CE.of_eq ?_, g⟩
    simp only
    rw [val_cat e, mul_assoc]
    congr 2
    rw [val, o3]
    simp [evalWord]
  · exact ⟨(stepRun_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH (ha.mono (by omega)) hf).1,
      (stepRun_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH (ha.mono (by omega)) hf).2.mono
        (by omega)⟩

variable (F THM E BS NB RD RW RA H x u) in
theorem walk_list (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1) (hE : E < 10)
    {X : ℕ → G} {r rot : ℕ} (hH : Hist RD RW RA H x u X r) (ps : List ℕ) :
    ∀ (st : WS) (B : ℕ), 2 ^ 21 ≤ B → B + 2 * ps.length < 2 ^ 22 → GW B st.2 →
    wsFail (ps.foldl (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st).1 = 0 →
    CE H (X (wsK st.1) * val x st.2 * (ps.map (pv x u E rot)).prod)
      (X (wsK (ps.foldl (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st).1) *
        val x (ps.foldl (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st).2) ∧
    GW (B + 2 * ps.length) (ps.foldl (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st).2 := by
  induction ps with
  | nil =>
    intro st B _ _ ha _
    exact ⟨CE.of_eq (by simp), by simpa using ha⟩
  | cons p ps ih =>
    intro st B hB1 hB2 ha hf
    simp only [List.foldl_cons, List.length_cons, List.map_cons, List.prod_cons] at hf hB2 ⊢
    have hf1 : wsFail (walkStep F THM E BS NB RD RW RA r rot p st).1 = 0 := by
      have := wsFail_lt (walkStep F THM E BS NB RD RW RA r rot p st).1
      by_contra hne
      have h1 := foldl_fail (F := F) (THM := THM) (E := E) (BS := BS) (NB := NB) (RD := RD)
        (RW := RW) (RA := RA) r rot ps (st := walkStep F THM E BS NB RD RW RA r rot p st)
        (by omega)
      omega
    obtain ⟨c1, g1⟩ := walkStep_spec F RD RW RA THM E BS NB H x u hx hu hθ hone hE hH hB1
      (by omega) ha hf1
    obtain ⟨c2, g2⟩ := ih _ (B + 2) (by omega) (by omega) g1 hf
    refine ⟨?_, by rw [show B + 2 * (ps.length + 1) = B + 2 + 2 * ps.length by omega]; exact g2⟩
    rw [← mul_assoc]
    exact (c1.mul_right _).trans c2

theorem prod_rec_eq {β : Sort*} (f : ℕ → ℕ → β) (p : WS) :
    Prod.rec (motive := fun _ => β) f p = f p.1 p.2 := rfl

@[expose] noncomputable def wR (r rot a n : ℕ) (down : Bool) (j : ℕ) : WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (walkStep F THM E BS NB RD RW RA r rot
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) down)
          (Prod.mk s' x'))))) st)
    j

theorem walkRun_eq (r rot a n : ℕ) (down : Bool) (st : WS) :
    walkRun F THM E BS NB RD RW RA r rot a n down st =
      ((List.range' 0 n).map (fun o => if down = true then a - o else a + o)).foldl
        (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st := by
  have key : ∀ j, j ≤ n → ∀ st : WS,
      wR (F := F) (THM := THM) (E := E) (BS := BS) (NB := NB) (RD := RD) (RW := RW) (RA := RA)
        r rot a n down j st =
      ((List.range' (n - j) j).map (fun o => if down = true then a - o else a + o)).foldl
        (fun st p => walkStep F THM E BS NB RD RW RA r rot p st) st := by
    intro j
    induction j with
    | zero => intro _ st; rfl
    | succ j ih =>
      intro hj st
      obtain ⟨s, x⟩ := st
      have e : wR (F := F) (THM := THM) (E := E) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
          (RA := RA) r rot a n down (j + 1) (s, x) =
          wR (F := F) (THM := THM) (E := E) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
          (RA := RA) r rot a n down j (walkStep F THM E BS NB RD RW RA r rot
            (if down = true then a - (n - 1 - j) else a + (n - 1 - j)) (s, x)) := by
        have e0 : wR (F := F) (THM := THM) (E := E) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
            (RA := RA) r rot a n down (j + 1) (s, x) = sW s (fun s' => sW x (fun x' =>
              wR (F := F) (THM := THM) (E := E) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
                (RA := RA) r rot a n down j (walkStep F THM E BS NB RD RW RA r rot
                  (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n 1) j))
                    (Nat.sub a (Nat.sub (Nat.sub n 1) j)) down) (s', x')))) := rfl
        rw [e0, sW_eq, sW_eq, brec_eq]
        rfl
      rw [e, ih (by omega), show n - (j + 1) = n - 1 - j by omega,
        show n - j = n - 1 - j + 1 by omega, List.range'_succ]
      rfl
  have := key n le_rfl st
  rw [Nat.sub_self] at this
  exact this

end Walk

section Relator

variable {x : ℕ → G} {u : G} {E : ℕ}

theorem relator_prod (hxE : x E * x E = 1) (hu : u * u = 1) (hE : (x E * u) ^ 4 = 1) {rot : ℕ}
    (hrot : rot < 2) : ((List.range' 0 8).map (pv x u E rot)).prod = 1 := by
  rw [show List.range' 0 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pv]
  interval_cases rot
  · simp only [pow_succ, pow_zero, one_mul] at hE
    norm_num
    simpa [mul_assoc] using hE
  · have h : u * (x E * u) ^ 4 * u = 1 := by rw [hE, mul_one, hu]
    norm_num
    simpa [pow_succ, mul_assoc, hu] using h

theorem prod_rev_inv {f : ℕ → G} (hf : ∀ p, f p * f p = 1) (l : List ℕ) :
    (l.reverse.map f).prod = ((l.map f).prod)⁻¹ := by
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  exact eq_inv_of_mul_eq_one_left (hf p)

theorem walk_relator (hx : ∀ c, x c * x c = 1) (hu : u * u = 1) (hE : (x E * u) ^ 4 = 1)
    {rot g : ℕ} (hrot : rot < 2) (hg : g < 8) (hgr : (g + rot) % 2 = 1) :
    (((List.range' 0 g).map (fun o => if false = true then 0 - o else 0 + o)).map
        (pv x u E rot)).prod * u =
      (((List.range' 0 (7 - g)).map (fun o => if true = true then 7 - o else 7 + o)).map
        (pv x u E rot)).prod := by
  have hpv : ∀ p, pv x u E rot p * pv x u E rot p = 1 := fun p => by
    unfold pv; split_ifs
    · exact hx E
    · exact hu
  have e1 : List.range' 0 8 = List.range' 0 g ++ g :: List.range' (g + 1) (7 - g) := by
    interval_cases g <;> rfl
  have e2 : (List.range' 0 (7 - g)).map (fun o => if true = true then 7 - o else 7 + o) =
      (List.range' (g + 1) (7 - g)).reverse := by
    interval_cases g <;> rfl
  have e3 : (List.range' 0 g).map (fun o => if false = true then 0 - o else 0 + o) =
      List.range' 0 g := by
    simp
  have hR := relator_prod (hx E) hu hE hrot
  rw [e1, List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hR
  have hgu : pv x u E rot g = u := by unfold pv; rw [if_neg (by omega)]
  rw [hgu, ← mul_assoc] at hR
  rw [e2, e3, prod_rev_inv hpv, eq_inv_of_mul_eq_one_left hR]

end Relator

section Records

variable {F RD RW RA : ℕ → ℕ} {THM E BS NB : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}

theorem val_eq_of_isOne (hx : ∀ c, x c * x c = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {A B v w : ℕ} (hv : GW A v) (hw : GW B w) (hAB : A + B ≤ 2 ^ 32)
    (h : isOne F BS NB (wCat (wRev v) w) = true) : val x v = val x w := by
  obtain ⟨g, e⟩ := GW.cat hv.rev.1 hw hAB
  have := val_one hone g.lt h
  rw [val_cat e, val_rev hx] at this
  exact inv_mul_eq_one.mp this

theorem land_one (n : ℕ) : Nat.land n 1 = n % 2 := Nat.and_one_is_mod n

theorem wsK_wsMk {k : ℕ} (hk : k < 256) (J : ℕ) : wsK (wsMk k 0 J) = k :=
  (wsMk_spec hk (by norm_num) J).1

variable (F THM E BS NB RD RW RA H x u) in
theorem walkOK_spec (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hE : E < 10 → (x E * u) ^ 4 = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r d J : ℕ} (hH : Hist RD RW RA H x u X r) (hRW : GW (2 ^ 20) (RW r))
    (hRA : GW (2 ^ 20) (RA r)) (h : walkOK F THM E BS NB RD RW RA r d J = true) :
    CE H (X (dN1 d) * val x (RW r) * u) (X (dN2 d) * val x (RA r)) := by
  unfold walkOK at h
  simp only [sB_eq, prod_rec_eq, andB_iff, walkRun_eq] at h
  obtain ⟨hh0, hE10, hgr, hff, hfb, -, hkf, hkb, h1f, h1b⟩ := h
  replace hff := Nat.eq_of_beq_eq_true hff
  replace hfb := Nat.eq_of_beq_eq_true hfb
  have hE10' : E < 10 := Nat.blt_eq.mp hE10
  have hrot : Nat.land (hAfterWord (hDrop J 8)) 1 < 2 := by
    rw [land_one]; omega
  have hg : fld (hAfterWord (hDrop J 8)) 1 7 < 8 := fld_lt_succ _ _ _
  have hgr' : (fld (hAfterWord (hDrop J 8)) 1 7 + Nat.land (hAfterWord (hDrop J 8)) 1) % 2 = 1 := by
    have := Nat.eq_of_beq_eq_true hgr
    rw [land_one] at this
    exact this
  have hi : Nat.land J 255 < 256 := by
    have : Nat.land J 255 ≤ 255 := Nat.and_le_right
    omega
  have h0 : GW (2 ^ 21) (hWord (hDrop J 8)) :=
    ⟨(wInH_spec hh0).1, (wInH_spec hh0).2, lt_trans (hWord_spec _).1 (by norm_num)⟩
  obtain ⟨c1, g1⟩ := walk_list F RD RW RA THM E BS NB H x u hx hu hθ hone hE10' hH _ _ (2 ^ 21)
    le_rfl (by simp; omega) h0 hff
  obtain ⟨c2, g2⟩ := walk_list F RD RW RA THM E BS NB H x u hx hu hθ hone hE10' hH _ _ (2 ^ 21)
    le_rfl (by simp; omega) h0 hfb
  simp only [wsK_wsMk hi] at c1 c2
  rw [Nat.eq_of_beq_eq_true hkf] at c1
  rw [Nat.eq_of_beq_eq_true hkb] at c2
  rw [val_eq_of_isOne hx hone hRW g1 (by simp; omega) h1f,
    val_eq_of_isOne hx hone hRA g2 (by simp; omega) h1b]
  refine (c1.symm.mul_right u).trans ?_
  rw [mul_assoc _ _ u, walk_relator hx hu (hE hE10') hrot hg hgr']
  exact c2

variable (F THM BS NB RD RW RA H x u) in
theorem factStepOK_spec (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r d J : ℕ} (hH : Hist RD RW RA H x u X r) (hRW : GW (2 ^ 20) (RW r))
    (hRA : GW (2 ^ 20) (RA r)) (h : factStepOK F THM BS NB RD RW RA r d J = true) :
    CE H (X (dN1 d) * val x (RW r) * u) (X (dN2 d) * val x (RA r)) := by
  unfold factStepOK at h
  simp only [prod_rec_eq, andB_iff] at h
  obtain ⟨hf, hk, h1⟩ := h
  obtain ⟨c, g⟩ := stepRun_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH
    (hRW.mono (B' := 2 ^ 22) (by norm_num)) (Nat.eq_of_beq_eq_true hf)
  simp only [wsK_wsMk (dN1_lt d)] at c
  rw [Nat.eq_of_beq_eq_true hk, ← val_eq_of_isOne hx hone hRA g (by norm_num) h1] at c
  exact c

variable (F THM BS NB RD RW RA H x u) in
theorem diffOK_spec (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r d J : ℕ} (hH : Hist RD RW RA H x u X r) (hRW : GW (2 ^ 20) (RW r))
    (h : diffOK F THM BS NB RD RW RA r d J = true) :
    X (dN2 d) * val x (RW r) * (X (dN2 d))⁻¹ ∈ H := by
  unfold diffOK at h
  simp only [sB_eq, prod_rec_eq, andB_iff] at h
  obtain ⟨hh, hf1, hf2, hk1, hk2, h1⟩ := h
  have hi : Nat.land J 255 < 256 := by
    have : Nat.land J 255 ≤ 255 := Nat.and_le_right
    omega
  have h0 : GW (2 ^ 22) (hWord (hDrop J 8)) :=
    ⟨(wInH_spec hh).1, (wInH_spec hh).2, lt_trans (hWord_spec _).1 (by norm_num)⟩
  obtain ⟨c1, g1⟩ := stepRun_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH h0 (Nat.eq_of_beq_eq_true hf1)
  obtain ⟨c2, g2⟩ := stepRun_spec F RD RW RA THM BS NB H x u hx hu hθ hone hH h0 (Nat.eq_of_beq_eq_true hf2)
  simp only [wsK_wsMk hi] at c1 c2
  rw [Nat.eq_of_beq_eq_true hk1] at c1
  rw [Nat.eq_of_beq_eq_true hk2] at c2
  have c := c1.symm.trans c2
  obtain ⟨g3, e3⟩ := GW.cat g1 g2.rev.1 (by norm_num)
  rw [val_eq_of_isOne hx hone hRW g3 (by norm_num) h1, val_cat e3, val_rev hx]
  unfold CE at c
  convert c using 1
  group

end Records

end CFSG.Certificates.TwDce.Core

end

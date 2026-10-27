module

public import Certificates.Data.Kernel.Q16Q16K
public import CFSG.Certificates.Kernel.Census.E16Proof
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic

public section

namespace CFSG.KC.Q16Q16K

open CFSG.KC.Census CFSG.KC.Census.SP CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

theorem allL_eq_all (f : Rec → Bool) : ∀ L : List Rec, allL f L = L.all f
  | [] => rfl
  | a :: L => by
    change Bool.rec (motive := fun _ => Bool) false (allL f L) (f a) = (f a && L.all f)
    rw [allL_eq_all f L]
    cases f a <;> rfl

theorem allL_spec {f : Rec → Bool} {L : List Rec} (h : allL f L = true) {r : Rec} (hr : r ∈ L) :
    f r = true := by
  rw [allL_eq_all] at h
  exact List.all_eq_true.1 h r hr

theorem then_of {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem else_of {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

variable {n w : Nat}

theorem recOK_spec {r : Rec} (h : recOK n w r = true) :
    canon1 n w r.1 = true ∧ r.2.1 = pc n w r.1 r.1 ∧ r.2.2 = pc n w r.2.1 r.2.1 := by
  unfold recOK at h
  have hc1 : Nat.beq (Nat.shiftRight r.1 (Nat.mul n w)) (nat_lit 0) = true := by
    cases hc : Nat.beq (Nat.shiftRight r.1 (Nat.mul n w)) (nat_lit 0)
    · rw [hc] at h
      exact h
    · rfl
  have h1 := then_of h hc1
  have hc2 : Nat.beq r.2.1 (pc n w r.1 r.1) = true := by
    cases hc : Nat.beq r.2.1 (pc n w r.1 r.1)
    · rw [hc] at h1
      exact h1
    · rfl
  have hc3 := then_of h1 hc2
  exact ⟨hc1, Nat.eq_of_beq_eq_true hc2, Nat.eq_of_beq_eq_true hc3⟩

theorem recOK_mkRec {x : Nat} (hx : canon1 n w x = true) : recOK n w (mkRec n w x) = true := by
  have e : Nat.beq (Nat.shiftRight x (Nat.mul n w)) (nat_lit 0) = true := hx
  change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (Nat.beq (pc n w (pc n w x x) (pc n w x x)) (pc n w (pc n w x x) (pc n w x x)))
    (Nat.beq (pc n w x x) (pc n w x x))) (Nat.beq (Nat.shiftRight x (Nat.mul n w)) (nat_lit 0)) = true
  rw [e, Nat.beq_refl, Nat.beq_refl]

theorem q16K_sound (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) {gs : Array Nat} {ps : List Nat}
    {c : ArrCertP} {R : List Rec} (hps : ∀ p ∈ ps, p < n)
    (hg : gs.toList.all (canon1 n w) = true) (hpts : c.pts.toList = R.map Prod.fst)
    (hrec : R.all (recOK n w) = true) (henum : penumOK n w gs ps c = true)
    (hfree : R.all (chkX n w R) = true) :
    Nat.card ↥(Subgroup.closure (permsA n (gs.map (unpackP n w)))) = R.length ∧
      NoQ16Q16 ↥(Subgroup.closure (permsA n (gs.map (unpackP n w)))) := by
  have hR : ∀ r ∈ R, recOK n w r = true := List.all_eq_true.1 hrec
  have hc : c.pts.toList.all (canon1 n w) = true := by
    rw [hpts, List.all_eq_true]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact (recOK_spec (hR r hr)).1
  have G : Good n w := by
    have h' := henum
    unfold penumOK at h'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨-, ⟨⟨h0, hid⟩, -⟩, -⟩ := h'
    have hv0 := pvalid_pts_of_penumOK henum c.pts[0]! (by
      rw [getElem!_pos c.pts 0 h0]
      exact Array.getElem_mem_toList h0)
    rw [hid] at hv0
    obtain ⟨e1, e2⟩ := pid_good hw hv0
    exact ⟨hn, hw, e1, e2⟩
  have hE := enumOK_of_enumOKK (penumOK_sound hn hw hg hc henum)
  obtain ⟨-, hcard, -⟩ := enumOK_spec hps hE
  have hsize : (c.toMain n w).pts.size = R.length := by
    simp only [ArrCertP.toMain, Array.size_map]
    rw [← Array.length_toList, hpts, List.length_map]
  refine ⟨hcard.trans hsize, ?_⟩
  have hrep : ∀ g ∈ Subgroup.closure (permsA n (gs.map (unpackP n w))),
      ∃ r ∈ R, Rep n (unpackP n w r.1) g := by
    intro g hg'
    obtain ⟨i, hi, hr⟩ := enumOK_exists_rep hps hE hg'
    have hi' : i < c.pts.size := by simpa [ArrCertP.toMain] using hi
    have hmem : c.pts[i]! ∈ R.map Prod.fst := by
      rw [← hpts, getElem!_pos c.pts i hi']
      exact Array.getElem_mem_toList hi'
    obtain ⟨r, hr', he⟩ := List.mem_map.1 hmem
    refine ⟨r, hr', ?_⟩
    have e : (c.toMain n w).pts[i]! = unpackP n w c.pts[i]! := map_get _ _ hi'
    rw [he, ← e]
    exact hr
  have hcan : ∀ r ∈ R, canon1 n w r.1 = true ∧ canon1 n w r.2.1 = true ∧
      canon1 n w r.2.2 = true := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := recOK_spec (hR r hr)
    exact ⟨h1, h2 ▸ pc_canon G _ _, h3 ▸ pc_canon G _ _⟩
  have hsq : ∀ r ∈ R, ∀ {g : Equiv.Perm (Fin n)}, Rep n (unpackP n w r.1) g →
      Rep n (unpackP n w r.2.1) (g * g) ∧ Rep n (unpackP n w r.2.2) (g * g * (g * g)) := by
    intro r hr g hg'
    obtain ⟨h1, h2, h3⟩ := recOK_spec (hR r hr)
    have hs : Rep n (unpackP n w r.2.1) (g * g) := by
      rw [h2, pc_eq G h1]
      exact rep_compA hg' hg'
    refine ⟨hs, ?_⟩
    rw [h3, pc_eq G (hcan r hr).2.1]
    exact rep_compA hs hs
  have hpc : ∀ {p q : Nat} {g h : Equiv.Perm (Fin n)}, canon1 n w p = true →
      Rep n (unpackP n w p) g → Rep n (unpackP n w q) h → Rep n (unpackP n w (pc n w p q)) (g * h) :=
    fun hp hg' hh => by
      rw [pc_eq G hp]
      exact rep_compA hg' hh
  have hbeq : ∀ {p q : Nat} {g h : Equiv.Perm (Fin n)}, canon1 n w p = true →
      canon1 n w q = true → Rep n (unpackP n w p) g → Rep n (unpackP n w q) h → g = h →
      Nat.beq p q = true := fun hp hq hg' hh e => by
    rw [← eqA_unpack hp hq]
    exact (eqA_iff hg' hh).2 e
  have hid : Rep n (unpackP n w (pid n w)) 1 := by
    rw [G.pid_eq]
    exact rep_idA
  have hcm : ∀ {p q : Nat} {g h : Equiv.Perm (Fin n)}, canon1 n w p = true →
      canon1 n w q = true → Rep n (unpackP n w p) g → Rep n (unpackP n w q) h → g * h = h * g →
      cm n w p q = true := fun hp hq hg' hh e =>
    hbeq (pc_canon G _ _) (pc_canon G _ _) (hpc hp hg' hh) (hpc hq hh hg') e
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨x', hx'⟩ ⟨y', hy'⟩ hq
  have hq' : Q16Q16 x y x' y' :=
    Q16Q16.map (Subgroup.closure (permsA n (gs.map (unpackP n w)))).subtype
      (Subgroup.subtype_injective _) hq
  obtain ⟨⟨hx4, hx8, hy2, hyx⟩, ⟨-, -, hy'2, hy'x'⟩, h44, hxx', hxy', hyx', hyy'⟩ := hq'
  obtain ⟨a, ha, ra⟩ := hrep x hx
  obtain ⟨b, hb, rb⟩ := hrep y hy
  obtain ⟨k, hk, rk⟩ := hrep x' hx'
  obtain ⟨l, hl, rl⟩ := hrep y' hy'
  obtain ⟨ca1, -, ca3⟩ := hcan a ha
  obtain ⟨cb1, cb2, -⟩ := hcan b hb
  obtain ⟨ck1, -, ck3⟩ := hcan k hk
  obtain ⟨cl1, cl2, -⟩ := hcan l hl
  have p4 : ∀ g : Equiv.Perm (Fin n), g ^ 4 = g * g * (g * g) := fun g => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have p8 : ∀ g : Equiv.Perm (Fin n), g ^ 8 = g * g * (g * g) * (g * g * (g * g)) := fun g => by
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, p4]
  have hinv : ∀ {u v : Equiv.Perm (Fin n)}, v * u * v⁻¹ = u⁻¹ → u * (v * u) = v := by
    intro u v e
    have e' : v * u = u⁻¹ * v := by
      have := congrArg (· * v) e
      simpa [mul_assoc] using this
    rw [e', ← mul_assoc, mul_inv_cancel, one_mul]
  have hX := List.all_eq_true.1 hfree a ha
  unfold chkX at hX
  have hX1 := else_of hX (Bool.eq_false_iff.2 fun h => hx4 (by
    rw [p4]
    exact (eqA_iff (hsq a ha ra).2 hid).1 (by rw [eqA_unpack ca3 G.pid_canon]; exact h)))
  have hY := then_of hX1 (hbeq (pc_canon G _ _) G.pid_canon
    (hpc ca3 (hsq a ha ra).2 (hsq a ha ra).2) hid (by rw [← p8]; exact hx8))
  have hY' := allL_spec hY hb
  unfold chkY at hY'
  have hK := then_of (then_of hY' (hbeq cb2 ca3 (hsq b hb rb).1 (hsq a ha ra).2
    (by rw [← p4, ← hy2, pow_two])))
    (hbeq (pc_canon G _ _) cb1 (hpc ca1 ra (hpc cb1 rb ra)) rb (hinv hyx))
  have hK' := allL_spec hK hk
  unfold chkK at hK'
  have hL := then_of (then_of (then_of hK' (hbeq ck3 ca3 (hsq k hk rk).2 (hsq a ha ra).2
    (by rw [← p4, ← p4]; exact h44.symm)))
    (hcm ca1 ck1 ra rk hxx')) (hcm cb1 ck1 rb rk hyx')
  have hL' := allL_spec hL hl
  unfold chkL at hL'
  have h0 := then_of (then_of (then_of (then_of hL' (hbeq cl2 ca3 (hsq l hl rl).1 (hsq a ha ra).2
    (by rw [← p4, h44, ← hy'2, pow_two])))
    (hbeq (pc_canon G _ _) cl1 (hpc ck1 rk (hpc cl1 rl rk)) rl (hinv hy'x')))
    (hcm ca1 cl1 ra rl hxy')) (hcm cb1 cl1 rb rl hyy')
  exact Bool.false_ne_true h0

end CFSG.KC.Q16Q16K

end

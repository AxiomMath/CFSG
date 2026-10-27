module

public import Certificates.Data.Kernel.OctadBig
public import CFSG.Certificates.Kernel.CompatSound
public import Certificates.Certificate24850

public section

namespace CFSG.KC.OctadBig

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.S CFSG.KC.Sym6Sq
  CFSG.KC.Compat CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std

theorem elt4_code (B : List S24) (m : ℕ) : eltK 24 4 (B.map cd) m = cd (m24Elt4 B m) := by
  have h := eltK_loop (by norm_num) _ B m 4 1 0
  have h1 : one 24 = codeP ((1 : S24) : Perm (Fin 24)) := c1S
  rw [Nat.pow_zero, Nat.div_one, ← List.range_eq_range', ← h1] at h
  rw [m24Elt4, eltK]
  exact h

@[expose] def repC : List S24 := [1, pairC1, pairC2, pairC1 * pairC2]

theorem cosK_sound {E C : List S24} (hE : E.length = 64)
    (h : cosK (E.map cd) (m24B0l.map cd) (C.map cd) = true) :
    C.Nodup ∧ (∀ c ∈ C, c ∈ m24B0l) ∧ (∀ c ∈ C, ∀ c' ∈ C, ∃ c'' ∈ C, c * c' * c''⁻¹ ∈ E) ∧
      ∀ c ∈ C, ∀ c' ∈ C, c' * c⁻¹ ∈ E → c = c' := by
  unfold cosK at h
  rw [andB_iff, andB_iff, andB_iff, nodupK_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨List.Nodup.of_map cd h1, sub_of len_B h2, ?_, ?_⟩
  · intro c hc c' hc'
    rw [allL_iff] at h3
    have := h3 _ (List.mem_map_of_mem hc)
    rw [allL_iff] at this
    have := this _ (List.mem_map_of_mem hc')
    rw [anyL_iff] at this
    obtain ⟨u, hu, hu'⟩ := this
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.1 hu
    rw [cd_mul, cd_inv, cd_mul, memI_iff _ hE] at hu'
    exact ⟨c'', hc'', hu'⟩
  · intro c hc c' hc' hcc
    rw [allL_iff] at h4
    have := h4 _ (List.mem_map_of_mem hc)
    rw [allL_iff] at this
    have := this _ (List.mem_map_of_mem hc')
    rw [impB_iff, cd_inv, cd_mul, memI_iff _ hE, beq_iff] at this
    exact cd_inj (this hcc)

theorem ordK_sound (p : S24) (r : ℕ) (h : ordK (m24B0l.map cd) (cd p) r = true) :
    OrdNormB0 p r := by
  unfold ordK at h
  rw [andB_iff, andB_iff, notB_iff, beq_iff, beq_iff, strictA_eq, cd_inv] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hp : pow 24 (cd p) r = cd (p ^ r) := by
    have e := LQT.P.code_pow (n := 24) (by norm_num) (p : Perm (Fin 24)) r
    rw [← Subgroup.coe_pow] at e
    exact e
  rw [hp, cd_one] at h1
  rw [cd_one] at h2
  exact ⟨cd_inj h1, fun e => h2 (congrArg cd e), conj_of p len_B h3⟩

theorem flat_eq (L : List S24) :
    (L.flatMap fun a => [a, a * pairC1, a * pairC2, a * (pairC1 * pairC2)].map
      (normH NativeSporadic.M24)) = L.flatMap fun a => repC.map (a * ·) := by
  simp only [repC, List.map_cons, List.map_nil, normH_eq, mul_one]

theorem pairL256_eq : pairL256 = m24E1l.flatMap fun a => repC.map (a * ·) := flat_eq m24E1l

theorem octad_list
    (hcp : CompatPairData)
    (hcos : repC.Nodup ∧ (∀ c ∈ repC, c ∈ m24B0l) ∧
      (∀ c ∈ repC, ∀ c' ∈ repC, ∃ c'' ∈ repC, c * c' * c''⁻¹ ∈ m24E1l) ∧
      ∀ c ∈ repC, ∀ c' ∈ repC, c' * c⁻¹ ∈ m24E1l → c = c') :
    pairL256.length = 256 ∧ pairL256.Nodup ∧ (1 : S24) ∈ pairL256 ∧
      (∀ x ∈ pairL256, ∀ y ∈ pairL256, x * y ∈ pairL256) ∧
      (∀ x ∈ pairL256, ∀ b ∈ m24B0l, x * b * x⁻¹ ∈ m24B0l) := by
  obtain ⟨hElen, hEnd, hE1, hEmul, hEsq, -, -⟩ := Certificates.certificate4137.1
  obtain ⟨-, -, -, -, -, hBcomm⟩ := Certificates.certificate24850
  obtain ⟨hAB, hBA, -, -⟩ := hcp
  obtain ⟨hCnd, hCB, hCmul, hCinj⟩ := hcos
  have hEinv : ∀ a ∈ m24E1l, a⁻¹ ∈ m24E1l := fun a ha => by
    rw [inv_eq_of_mul_eq_one_right (hEsq a ha)]
    exact ha
  have hmem : ∀ x, x ∈ pairL256 ↔ ∃ a ∈ m24E1l, ∃ c ∈ repC, x = a * c := by
    intro x
    rw [pairL256_eq, List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hx⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      exact ⟨a, ha, c, hc, rfl⟩
    · rintro ⟨a, ha, c, hc, rfl⟩
      exact ⟨a, ha, List.mem_map.2 ⟨c, hc, rfl⟩⟩
  have h1C : (1 : S24) ∈ repC := by simp [repC]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pairL256_eq, List.length_flatMap]
    have : ∀ a : S24, (repC.map (a * ·)).length = 4 := fun a => by simp [repC]
    simp only [this, List.map_const', List.sum_replicate, smul_eq_mul, hElen]
  · rw [pairL256_eq, List.nodup_flatMap]
    refine ⟨fun a _ => hCnd.map (mul_right_injective a), ?_⟩
    refine hEnd.imp_of_mem fun {a a'} ha ha' hne => ?_
    intro z hz hz'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
    obtain ⟨c', hc', e⟩ := List.mem_map.1 hz'
    have hcc : c * c'⁻¹ ∈ m24E1l := by
      have : c * c'⁻¹ = a⁻¹ * a' := by
        calc c * c'⁻¹ = a⁻¹ * (a * c) * c'⁻¹ := by group
          _ = a⁻¹ * (a' * c') * c'⁻¹ := by rw [e]
          _ = a⁻¹ * a' := by group
      rw [this]
      exact hEmul _ (hEinv a ha) _ ha'
    have := hCinj c' hc' c hc hcc
    subst this
    exact hne (mul_right_cancel e).symm
  · rw [hmem]
    exact ⟨1, hE1, 1, h1C, (mul_one 1).symm⟩
  · intro x hx y hy
    rw [hmem] at hx hy ⊢
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    obtain ⟨a', ha', c', hc', rfl⟩ := hy
    obtain ⟨c'', hc'', he⟩ := hCmul c hc c' hc'
    refine ⟨a * (c * a' * c⁻¹) * (c * c' * c''⁻¹), ?_, c'', hc'', by group⟩
    exact hEmul _ (hEmul _ ha _ (hBA c (hCB c hc) a' ha')) _ he
  · intro x hx b hb
    rw [hmem] at hx
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    have hcb : c * b * c⁻¹ = b := by
      rw [hBcomm c (hCB c hc) b hb]
      group
    have : a * c * b * (a * c)⁻¹ = a * (c * b * c⁻¹) * a⁻¹ := by group
    rw [this, hcb]
    exact hAB a ha b hb

theorem codeN {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) (w : List ℤ) :
    cd (pairN w) = evalZK 24 (pairGenW.map (evalZK 24 G)) w := by
  have hN : pairGens.map cd = pairGenW.map (evalZK 24 G) :=
    codes_gens NativeSporadic.M24 (by decide) [m24a, m24b] hG pairGenW
  have := codes_gens NativeSporadic.M24 (by decide) pairGens hN [w]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
  exact this

theorem obK_unfold {G : List ℕ} {rgw bw b0w nw : List (List ℤ)} {w3 w5 w7 : List ℤ}
    {E BB B : List ℕ} {c1 c2 : ℕ} (hE : lstK 24 6 (rlGK 24 G rgw bw) = E)
    (hBB : b0w.map (evalZK 24 G) = BB) (hB : lstK 24 4 BB = B) (h1 : eltK 24 4 BB 4 = c1)
    (h2 : eltK 24 4 BB 8 = c2) :
    obK G rgw bw b0w nw w3 w5 w7 =
      CFSG.KC.Ord.andB (cosK E B [one 24, c1, c2, mul 24 c1 c2])
        (CFSG.KC.Ord.andB (ordK B (evalZK 24 (nw.map (evalZK 24 G)) w3) 3)
          (CFSG.KC.Ord.andB (ordK B (evalZK 24 (nw.map (evalZK 24 G)) w5) 5)
            (ordK B (evalZK 24 (nw.map (evalZK 24 G)) w7) 7))) := by
  unfold obK
  rw [forceA_eq, hE, forceA_eq, hBB, forceA_eq, hB, strictA_eq, strictA_eq, h1, h2, forceA_eq]

theorem octadBig_of {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (hcp : CompatPairData)
    (h : obK G m24RGens m24E1Bw m24B0Bw pairGenW
      [-1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1]
      [1, 2, 1, 2, 1, 2] [-1, 1, 1, -2, -1, 1, 1, -2] = true) : OctadBigData := by
  have hE : m24E1l.map cd = lstK 24 6 (rlGK 24 G m24RGens m24E1Bw) := codesE hG
  have hB0 : m24B0B.map cd = m24B0Bw.map (evalZK 24 G) :=
    codes_gens NativeSporadic.M24 (by decide) [m24a, m24b] hG m24B0Bw
  have hB : m24B0l.map cd = lstK 24 4 (m24B0B.map cd) := lst4_codes m24B0B rfl
  have e1 : eltK 24 4 (m24B0B.map cd) 4 = cd pairC1 := elt4_code m24B0B 4
  have e2 : eltK 24 4 (m24B0B.map cd) 8 = cd pairC2 := elt4_code m24B0B 8
  have h3 : cd pairOrd3 = evalZK 24 (pairGenW.map (evalZK 24 G))
      [-1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1] := codeN hG _
  have h5 : cd pairOrd5 = evalZK 24 (pairGenW.map (evalZK 24 G)) [1, 2, 1, 2, 1, 2] :=
    codeN hG _
  have h7 : cd pairOrd7 = evalZK 24 (pairGenW.map (evalZK 24 G)) [-1, 1, 1, -2, -1, 1, 1, -2] :=
    codeN hG _
  rw [obK_unfold hE.symm hB0.symm hB.symm e1 e2, ← h3, ← h5, ← h7, cd_one, cd_mul, andB_iff,
    andB_iff, andB_iff] at h
  obtain ⟨hc, ho3, ho5, ho7⟩ := h
  have hrep : [cd 1, cd pairC1, cd pairC2, cd (pairC1 * pairC2)] = repC.map cd := rfl
  rw [hrep] at hc
  obtain ⟨l1, l2, l3, l4, l5⟩ := octad_list hcp (cosK_sound len_E hc)
  exact ⟨l1, l2, l3, l4, l5, ordK_sound _ _ ho3, ordK_sound _ _ ho5, ordK_sound _ _ ho7⟩

end CFSG.KC.OctadBig

end

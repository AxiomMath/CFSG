module

public import CFSG.CGT.Hall82.DBasic

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G} {Q : Subgroup G} {S : Setting G M L}

private structure Hyp (S : Setting G M L) (R : Subgroup G) (rep : Fin 64 → G)
    (Q : Subgroup G) : Type where
  hF : ModelFacts
  hD : DModelFacts
  hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep
  hC1 : Subgroup.centralizer (L : Set G) = ⊥
  Φ : ↥M →* Equiv.Perm (Fin 64)
  hΦinj : Function.Injective Φ
  hΦ : ∀ m : ↥M, ∃ a : Fin 64, Φ m = transl a * S.psiM hc m
  hΦrep : ∀ (m : ↥M) (b : Fin 64), (m : G) = rep b → Φ m = transl b
  hQM : Q ≤ M
  hQc : Q ≤ Subgroup.centralizer ({rep 5} : Set G)
  hQn : ∀ g ∈ Subgroup.centralizer ({rep 5} : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  hQV : ∀ v, rep v ∈ Q ↔ InHallU v
  hψQ : S.psiSub hc Q = hallRM
  hψM : S.psiSub hc M = hexaM
  hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = rep 5
  hQsq : ∀ a ∈ Q, a * a = 1 ∨ a * a = rep 5
  h34 : ∀ (g : G) (h h' : Fin 64), IsOvalVec h → IsOvalVec h' →
    g * rep h * g⁻¹ = rep h' → g ∈ M

namespace Hyp

private lemma psi_eq_one_iff_mem_blockU (H : Hyp S R rep Q) {m : G} (hm : m ∈ M) :
    S.psiM H.hc ⟨m, hm⟩ = 1 ↔ m ∈ blockU L :=
  S.psiM_eq_one_iff_mem_blockU H.hc H.hC1 ⟨m, hm⟩

private noncomputable def psiQ (H : Hyp S R rep Q) : ↥Q →* Equiv.Perm (Fin 64) :=
  (S.psiM H.hc).comp (Subgroup.inclusion H.hQM)

private noncomputable def phiQ (H : Hyp S R rep Q) : ↥Q →* Equiv.Perm (Fin 64) :=
  H.Φ.comp (Subgroup.inclusion H.hQM)

private lemma psiQ_apply (H : Hyp S R rep Q) (q : ↥Q) :
    psiQ H q = S.psiM H.hc ⟨(q : G), H.hQM q.2⟩ := rfl

private lemma phiQ_apply (H : Hyp S R rep Q) (q : ↥Q) :
    phiQ H q = H.Φ ⟨(q : G), H.hQM q.2⟩ := rfl

private lemma range_psiQ (H : Hyp S R rep Q) : (psiQ H).range = hallRM := by
  rw [show (psiQ H).range = S.psiSub H.hc Q from ?_, H.hψQ]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    rw [mem_psiSub S H.hc H.hQM]
    exact ⟨(q : G), q.2, H.hQM q.2, rfl⟩
  · intro hx
    rw [mem_psiSub S H.hc H.hQM] at hx
    obtain ⟨q, hq, hqM, hqx⟩ := hx
    refine ⟨⟨q, hq⟩, ?_⟩
    simpa [psiQ_apply] using hqx

private lemma psiQ_mem_hallRM (H : Hyp S R rep Q) (q : ↥Q) : psiQ H q ∈ hallRM := by
  have h : psiQ H q ∈ (psiQ H).range := ⟨q, rfl⟩
  rwa [range_psiQ H] at h

private lemma psiQ_eq_one_iff (H : Hyp S R rep Q) (q : ↥Q) :
    psiQ H q = 1 ↔ ∃ v, InHallU v ∧ (q : G) = rep v := by
  rw [psiQ_apply, psi_eq_one_iff_mem_blockU H (H.hQM q.2)]
  constructor
  · intro hqV
    obtain ⟨v, hv⟩ := H.hc.surj (q : G) hqV
    exact ⟨v, (H.hQV v).mp (hv ▸ q.2), hv.symm⟩
  · rintro ⟨v, hvU, hqv⟩
    rw [hqv]
    exact H.hc.mem v

private lemma rep5_mem_Q (H : Hyp S R rep Q) : rep 5 ∈ Q := (H.hQV 5).mpr (by decide)

private lemma rep5_ne_one (H : Hyp S R rep Q) : rep 5 ≠ 1 := fun h =>
  absurd ((rep_eq_one_iff H.hc).mp h) (by decide)

private noncomputable def cQ (H : Hyp S R rep Q) : ↥Q := ⟨rep 5, rep5_mem_Q H⟩

private lemma cQ_apply (H : Hyp S R rep Q) : (cQ H : G) = rep 5 := rfl

private lemma commute_cQ (H : Hyp S R rep Q) (q : ↥Q) :
    (cQ H : G) * (q : G) = (q : G) * rep 5 := by
  rw [cQ_apply]
  exact Subgroup.mem_centralizer_iff.mp (H.hQc q.2) (rep 5) (by simp)

private lemma hallRMPerm_zero (H : Hyp S R rep Q) : hallRMPerm 0 = 1 := by
  have h := H.hD.rm_mul 0 0
  have h00 : xor8 0 0 = 0 := by decide
  rw [h00] at h
  have h' : hallRMPerm 0 * 1 = hallRMPerm 0 * hallRMPerm 0 := by
    rw [mul_one, h]
  exact (mul_left_cancel h').symm

private lemma hallRMPerm_prod (H : Hyp S R rep Q) (e : Fin 8) :
    hallRMPerm (hallRIdx 0) ^ (e.val % 2) *
      hallRMPerm (hallRIdx 1) ^ (e.val / 2 % 2) *
      hallRMPerm (hallRIdx 2) ^ (e.val / 4 % 2) = hallRMPerm e := by
  fin_cases e <;>
    simp [hallRIdx, hallRMPerm_zero H, H.hD.rm_mul, show xor8 1 2 = 3 from by decide,
      show xor8 1 4 = 5 from by decide, show xor8 2 4 = 6 from by decide,
      show xor8 1 1 = 0 from by decide, show xor8 2 2 = 0 from by decide,
      show xor8 4 4 = 0 from by decide, show xor8 3 4 = 7 from by decide]

private lemma rep_mem_M (H : Hyp S R rep Q) (b : Fin 64) : rep b ∈ M :=
  S.blockU_le (H.hc.mem b)

private lemma phi_rep (H : Hyp S R rep Q) (b : Fin 64) :
    H.Φ ⟨rep b, rep_mem_M H b⟩ = transl b :=
  H.hΦrep ⟨rep b, rep_mem_M H b⟩ b rfl

private lemma psi_rep (H : Hyp S R rep Q) (b : Fin 64) :
    S.psiM H.hc ⟨rep b, rep_mem_M H b⟩ = 1 :=
  (psi_eq_one_iff_mem_blockU H (rep_mem_M H b)).mpr (H.hc.mem b)

private lemma mem_centralizer_of_psi_five (H : Hyp S R rep Q) {m : G} (hmM : m ∈ M)
    (h5 : S.psiM H.hc ⟨m, hmM⟩ 5 = 5) :
    m ∈ Subgroup.centralizer ({rep 5} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  have hconj := (S.conj_rep_eq_iff H.hc ⟨m, hmM⟩ 5).mpr h5
  exact (calc m * rep 5 = (m * rep 5 * m⁻¹) * m := by group
    _ = rep 5 * m := by rw [hconj]).symm

private lemma exists_mem_M_of_mem_hexaM (H : Hyp S R rep Q) {s : Equiv.Perm (Fin 64)}
    (hs : s ∈ hexaM) : ∃ m : G, ∃ hm : m ∈ M, S.psiM H.hc ⟨m, hm⟩ = s := by
  have hsm : s ∈ S.psiSub H.hc M := by rw [H.hψM]; exact hs
  rw [mem_psiSub S H.hc (le_refl M)] at hsm
  obtain ⟨m, -, hmM, hψm⟩ := hsm
  exact ⟨m, hmM, hψm⟩

private lemma exists_lift (H : Hyp S R rep Q) {s : Equiv.Perm (Fin 64)} (hs : s ∈ hexaM)
    (hs5 : s 5 = 5) (b : Fin 64) :
    ∃ m : G, ∃ hmM : m ∈ M, m ∈ Subgroup.centralizer ({rep 5} : Set G) ∧
      S.psiM H.hc ⟨m, hmM⟩ = s ∧ H.Φ ⟨m, hmM⟩ = transl b * s := by
  obtain ⟨m, hmM, hψm⟩ := exists_mem_M_of_mem_hexaM H hs
  obtain ⟨b', hb'⟩ := H.hΦ ⟨m, hmM⟩
  let m' : G := rep (xorF b b') * m
  have hm'M : m' ∈ M := M.mul_mem (rep_mem_M H (xorF b b')) hmM
  have hm'sub : (⟨m', hm'M⟩ : ↥M) =
      ⟨rep (xorF b b'), rep_mem_M H (xorF b b')⟩ * ⟨m, hmM⟩ := by
    apply Subtype.ext
    rfl
  have hψm' : S.psiM H.hc ⟨m', hm'M⟩ = s := by
    rw [hm'sub, map_mul, psi_rep H (xorF b b'), hψm, one_mul]
  have hΦm' : H.Φ ⟨m', hm'M⟩ = transl b * s := by
    calc H.Φ ⟨m', hm'M⟩ = transl (xorF b b') * H.Φ ⟨m, hmM⟩ := by
          rw [hm'sub, map_mul, phi_rep H (xorF b b')]
      _ = transl (xorF b b') * (transl b' * s) := by rw [hb', hψm]
      _ = (transl b * transl b') * (transl b' * s) := by rw [transl_xorF]
      _ = transl b * s := by
            rw [mul_assoc (transl b) (transl b') (transl b' * s),
              ← mul_assoc (transl b') (transl b') s, transl_mul_self, one_mul]
  exact ⟨m', hm'M, mem_centralizer_of_psi_five H hm'M (by rw [hψm']; exact hs5), hψm', hΦm'⟩

private lemma hallXi_comm (H : Hyp S R rep Q) (q : Fin 3 → G) (hq : ∀ i, q i ∈ Q)
    (a : Fin 3 → Fin 64) (ha : ∀ i, H.Φ ⟨q i, H.hQM (hq i)⟩ = hallXi a i)
    (i j : Fin 3) :
    hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
      hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5 := by
  let c : G := q i * q j * (q i)⁻¹ * (q j)⁻¹
  have hcQ : c ∈ Q := by
    dsimp [c]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem (hq i) (hq j)) (Q.inv_mem (hq i)))
      (Q.inv_mem (hq j))
  have hmap : H.Φ ⟨c, H.hQM hcQ⟩ =
      hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ := by
    have hsub : (⟨c, H.hQM hcQ⟩ : ↥M) =
        ⟨q i, H.hQM (hq i)⟩ * ⟨q j, H.hQM (hq j)⟩ * ⟨q i, H.hQM (hq i)⟩⁻¹ *
          ⟨q j, H.hQM (hq j)⟩⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hsub]
    simp only [map_mul, map_inv, ha i, ha j]
  rcases H.hQcomm (q i) (hq i) (q j) (hq j) with h1 | h5
  · left
    rw [← hmap, show (⟨c, H.hQM hcQ⟩ : ↥M) = 1 by ext; exact h1]
    exact map_one H.Φ
  · right
    rw [← hmap, show (⟨c, H.hQM hcQ⟩ : ↥M) = ⟨rep 5, H.hQM (rep5_mem_Q H)⟩ by ext; exact h5]
    exact H.hΦrep ⟨rep 5, H.hQM (rep5_mem_Q H)⟩ 5 rfl

private lemma hallXi_sq (H : Hyp S R rep Q) (q : Fin 3 → G) (hq : ∀ i, q i ∈ Q)
    (a : Fin 3 → Fin 64) (ha : ∀ i, H.Φ ⟨q i, H.hQM (hq i)⟩ = hallXi a i)
    (i : Fin 3) :
    hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5 := by
  let c : G := q i * q i
  have hcQ : c ∈ Q := by
    dsimp [c]
    exact Q.mul_mem (hq i) (hq i)
  have hmap : H.Φ ⟨c, H.hQM hcQ⟩ = hallXi a i * hallXi a i := by
    have hsub : (⟨c, H.hQM hcQ⟩ : ↥M) =
        ⟨q i, H.hQM (hq i)⟩ * ⟨q i, H.hQM (hq i)⟩ := by
      apply Subtype.ext
      rfl
    rw [hsub]
    simp only [map_mul, ha i]
  rcases H.hQsq (q i) (hq i) with h1 | h5
  · left
    rw [← hmap, show (⟨c, H.hQM hcQ⟩ : ↥M) = 1 by ext; exact h1]
    exact map_one H.Φ
  · right
    rw [← hmap, show (⟨c, H.hQM hcQ⟩ : ↥M) = ⟨rep 5, H.hQM (rep5_mem_Q H)⟩ by ext; exact h5]
    exact H.hΦrep ⟨rep 5, H.hQM (rep5_mem_Q H)⟩ 5 rfl

private lemma hallXi_conj (H : Hyp S R rep Q) (q : Fin 3 → G) (hq : ∀ i, q i ∈ Q)
    (hqψ : ∀ i, S.psiM H.hc ⟨q i, H.hQM (hq i)⟩ = hallRMPerm (hallRIdx i))
    (a : Fin 3 → Fin 64) (ha : ∀ i, H.Φ ⟨q i, H.hQM (hq i)⟩ = hallXi a i)
    {s : Equiv.Perm (Fin 64)} (hs : s ∈ hexaM) (hs5 : s 5 = 5) (i : Fin 3) :
    ∃ u, InHallU u ∧ ∃ e : Fin 8,
      s * hallXi a i * s⁻¹ = transl u * hallXProd a e := by
  classical
  obtain ⟨m', hm'M, hm'H, hψm', hΦm'⟩ := exists_lift H hs hs5 0
  rw [transl_zero, one_mul] at hΦm'
  let q' : G := m' * q i * m'⁻¹
  have hq'Q : q' ∈ Q := H.hQn m' hm'H (q i) (hq i)
  have hq'sub : (⟨q', H.hQM hq'Q⟩ : ↥M) =
      ⟨m', hm'M⟩ * ⟨q i, H.hQM (hq i)⟩ * ⟨m', hm'M⟩⁻¹ := by
    apply Subtype.ext
    rfl
  have hψq' : S.psiM H.hc ⟨q', H.hQM hq'Q⟩ = s * hallRMPerm (hallRIdx i) * s⁻¹ := by
    rw [hq'sub]
    simp only [map_mul, map_inv, hψm', hqψ i]
  have hrm : S.psiM H.hc ⟨q', H.hQM hq'Q⟩ ∈ hallRM := by
    have := psiQ_mem_hallRM H ⟨q', hq'Q⟩
    simpa [psiQ_apply] using this
  obtain ⟨e, he⟩ := (H.hD.mem_rm_iff _).mp hrm
  have hψq'e : S.psiM H.hc ⟨q', H.hQM hq'Q⟩ = hallRMPerm e := he.symm
  let e0 : ℕ := e.val % 2
  let e1 : ℕ := e.val / 2 % 2
  let e2 : ℕ := e.val / 4 % 2
  let prod : G := q 0 ^ e0 * q 1 ^ e1 * q 2 ^ e2
  have hprodQ : prod ∈ Q := by
    dsimp [prod]
    exact Q.mul_mem (Q.mul_mem (Q.pow_mem (hq 0) e0) (Q.pow_mem (hq 1) e1))
      (Q.pow_mem (hq 2) e2)
  have hprodsub : (⟨prod, H.hQM hprodQ⟩ : ↥M) =
      ⟨q 0, H.hQM (hq 0)⟩ ^ e0 * ⟨q 1, H.hQM (hq 1)⟩ ^ e1 *
        ⟨q 2, H.hQM (hq 2)⟩ ^ e2 := by
    apply Subtype.ext
    rfl
  have hψprod : S.psiM H.hc ⟨prod, H.hQM hprodQ⟩ = hallRMPerm e := by
    rw [hprodsub]
    simp only [map_mul, map_pow, hqψ 0, hqψ 1, hqψ 2]
    exact hallRMPerm_prod H e
  have hΦprod : H.Φ ⟨prod, H.hQM hprodQ⟩ = hallXProd a e := by
    rw [hprodsub]
    simp only [map_mul, map_pow, ha 0, ha 1, ha 2]
    rfl
  let d : G := q' * prod⁻¹
  have hdQ : d ∈ Q := Q.mul_mem hq'Q (Q.inv_mem hprodQ)
  have hdsub : (⟨d, H.hQM hdQ⟩ : ↥M) = ⟨q', H.hQM hq'Q⟩ * ⟨prod, H.hQM hprodQ⟩⁻¹ := by
    apply Subtype.ext
    rfl
  have hψd : S.psiM H.hc ⟨d, H.hQM hdQ⟩ = 1 := by
    rw [hdsub, map_mul, map_inv, hψq'e, hψprod, mul_inv_cancel]
  obtain ⟨u, huU, hdu⟩ := (psiQ_eq_one_iff H ⟨d, hdQ⟩).mp (by
    simpa [psiQ_apply] using hψd)
  have hdu' : d = rep u := hdu
  have hq'eq : q' = rep u * prod := by
    calc q' = d * prod := by dsimp [d]; group
      _ = rep u * prod := by rw [hdu']
  refine ⟨u, huU, e, ?_⟩
  have hq'Q' : rep u * prod ∈ Q :=
    Q.mul_mem ((H.hQV u).mpr huU) hprodQ
  have hΦq' : H.Φ ⟨q', H.hQM hq'Q⟩ = transl u * hallXProd a e := by
    rw [show (⟨q', H.hQM hq'Q⟩ : ↥M) = ⟨rep u * prod, H.hQM hq'Q'⟩ from
      Subtype.ext hq'eq]
    rw [show (⟨rep u * prod, H.hQM hq'Q'⟩ : ↥M) =
      ⟨rep u, rep_mem_M H u⟩ * ⟨prod, H.hQM hprodQ⟩ by ext; rfl]
    rw [map_mul, phi_rep H u, hΦprod]
  rw [← hΦq']
  rw [hq'sub]
  simp only [map_mul, map_inv, hΦm', ha i]

private lemma exists_basis (H : Hyp S R rep Q) :
    ∃ q : Fin 3 → G, ∃ hq : ∀ i, q i ∈ Q,
      (∀ i, S.psiM H.hc ⟨q i, H.hQM (hq i)⟩ = hallRMPerm (hallRIdx i)) ∧
      (∀ i, H.Φ ⟨q i, H.hQM (hq i)⟩ = hallRMPerm (hallRIdx i)) := by
  classical
  have hex : ∀ i, ∃ q : G, ∃ hq : q ∈ Q,
      S.psiM H.hc ⟨q, H.hQM hq⟩ = hallRMPerm (hallRIdx i) := by
    intro i
    have hmem : hallRMPerm (hallRIdx i) ∈ S.psiSub H.hc Q := by
      rw [H.hψQ]
      exact (H.hD.mem_rm_iff _).mpr ⟨hallRIdx i, rfl⟩
    rw [mem_psiSub S H.hc H.hQM] at hmem
    obtain ⟨q, hq, _, hqx⟩ := hmem
    exact ⟨q, hq, by simpa using hqx⟩
  choose q hq hqψ using hex
  choose a ha0 using fun i => H.hΦ ⟨q i, H.hQM (hq i)⟩
  have ha : ∀ i, H.Φ ⟨q i, H.hQM (hq i)⟩ = hallXi a i := by
    intro i
    rw [ha0 i, hqψ i]
    rfl
  have hU : ∀ i, InHallU (a i) :=
    H.hD.lift a (fun i j => hallXi_comm H q hq a ha i j)
      (fun i => hallXi_sq H q hq a ha i)
      (fun s hs hs5 i => hallXi_conj H q hq hqψ a ha hs hs5 i)
  refine ⟨fun i => rep (a i) * q i,
    fun i => Q.mul_mem ((H.hQV (a i)).mpr (hU i)) (hq i), ?_, ?_⟩
  · intro i
    have hsub : (⟨rep (a i) * q i, H.hQM (Q.mul_mem ((H.hQV (a i)).mpr (hU i)) (hq i))⟩ : ↥M) =
        ⟨rep (a i), rep_mem_M H (a i)⟩ * ⟨q i, H.hQM (hq i)⟩ := by
      apply Subtype.ext
      rfl
    rw [hsub, map_mul, psi_rep H (a i), hqψ i, one_mul]
  · intro i
    have hsub : (⟨rep (a i) * q i, H.hQM (Q.mul_mem ((H.hQV (a i)).mpr (hU i)) (hq i))⟩ : ↥M) =
        ⟨rep (a i), rep_mem_M H (a i)⟩ * ⟨q i, H.hQM (hq i)⟩ := by
      apply Subtype.ext
      rfl
    rw [hsub, map_mul, phi_rep H (a i), ha i, hallXi, ← mul_assoc, transl_mul_self, one_mul]

private noncomputable def basis (H : Hyp S R rep Q) : Fin 3 → G :=
  Classical.choose (exists_basis H)

private noncomputable def basis_mem (H : Hyp S R rep Q) : ∀ i, basis H i ∈ Q :=
  Classical.choose (Classical.choose_spec (exists_basis H))

private lemma basis_psi (H : Hyp S R rep Q) (i : Fin 3) :
    S.psiM H.hc ⟨basis H i, H.hQM (basis_mem H i)⟩ = hallRMPerm (hallRIdx i) :=
  (Classical.choose_spec (Classical.choose_spec (exists_basis H))).1 i

private lemma basis_phi (H : Hyp S R rep Q) (i : Fin 3) :
    H.Φ ⟨basis H i, H.hQM (basis_mem H i)⟩ = hallRMPerm (hallRIdx i) :=
  (Classical.choose_spec (Classical.choose_spec (exists_basis H))).2 i

private noncomputable def basisProd (H : Hyp S R rep Q) (e : Fin 8) : G :=
  basis H 0 ^ (e.val % 2) * basis H 1 ^ (e.val / 2 % 2) * basis H 2 ^ (e.val / 4 % 2)

private lemma basisProd_mem (H : Hyp S R rep Q) (e : Fin 8) : basisProd H e ∈ Q := by
  dsimp [basisProd]
  exact Q.mul_mem (Q.mul_mem (Q.pow_mem (basis_mem H 0) _) (Q.pow_mem (basis_mem H 1) _))
    (Q.pow_mem (basis_mem H 2) _)

private lemma basisProd_sub (H : Hyp S R rep Q) (e : Fin 8) :
    (⟨basisProd H e, H.hQM (basisProd_mem H e)⟩ : ↥M) =
      ⟨basis H 0, H.hQM (basis_mem H 0)⟩ ^ (e.val % 2) *
        ⟨basis H 1, H.hQM (basis_mem H 1)⟩ ^ (e.val / 2 % 2) *
        ⟨basis H 2, H.hQM (basis_mem H 2)⟩ ^ (e.val / 4 % 2) := by
  apply Subtype.ext
  rfl

private lemma basisProd_psi (H : Hyp S R rep Q) (e : Fin 8) :
    S.psiM H.hc ⟨basisProd H e, H.hQM (basisProd_mem H e)⟩ = hallRMPerm e := by
  rw [basisProd_sub]
  simp only [map_mul, map_pow, basis_psi]
  exact hallRMPerm_prod H e

private lemma basisProd_phi (H : Hyp S R rep Q) (e : Fin 8) :
    H.Φ ⟨basisProd H e, H.hQM (basisProd_mem H e)⟩ = hallRMPerm e := by
  rw [basisProd_sub]
  simp only [map_mul, map_pow, basis_phi]
  exact hallRMPerm_prod H e

private lemma phiQ_mem_hallX1 (H : Hyp S R rep Q) (q : ↥Q) : phiQ H q ∈ hallX1 := by
  have hψ := psiQ_mem_hallRM H q
  obtain ⟨e, he⟩ := (H.hD.mem_rm_iff _).mp hψ
  let d : G := (q : G) * (basisProd H e)⁻¹
  have hdQ : d ∈ Q := Q.mul_mem q.2 (Q.inv_mem (basisProd_mem H e))
  have hψq : S.psiM H.hc ⟨(q : G), H.hQM q.2⟩ = hallRMPerm e := by
    simpa [psiQ_apply] using he.symm
  have hψd : S.psiM H.hc ⟨d, H.hQM hdQ⟩ = 1 := by
    have hsub : (⟨d, H.hQM hdQ⟩ : ↥M) =
        ⟨(q : G), H.hQM q.2⟩ * ⟨basisProd H e, H.hQM (basisProd_mem H e)⟩⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hsub, map_mul, map_inv, hψq, basisProd_psi, mul_inv_cancel]
  obtain ⟨u, huU, hdu⟩ := (psiQ_eq_one_iff H ⟨d, hdQ⟩).mp (by
    simpa [psiQ_apply] using hψd)
  have hdu' : d = rep u := hdu
  have hqeq : (q : G) = rep u * basisProd H e := by
    calc (q : G) = d * basisProd H e := by dsimp [d]; group
      _ = rep u * basisProd H e := by rw [hdu']
  refine ⟨u, huU, e, ?_⟩
  have hqQ' : rep u * basisProd H e ∈ Q :=
    Q.mul_mem ((H.hQV u).mpr huU) (basisProd_mem H e)
  have hΦq : phiQ H q = transl u * hallRMPerm e := by
    rw [phiQ_apply]
    rw [show (⟨(q : G), H.hQM q.2⟩ : ↥M) = ⟨rep u * basisProd H e, H.hQM hqQ'⟩ from
      Subtype.ext hqeq]
    rw [show (⟨rep u * basisProd H e, H.hQM hqQ'⟩ : ↥M) =
      ⟨rep u, rep_mem_M H u⟩ * ⟨basisProd H e, H.hQM (basisProd_mem H e)⟩ by ext; rfl]
    rw [map_mul, phi_rep H u, basisProd_phi]
  exact hΦq

private lemma exists_phiQ_of_mem_hallX1 (H : Hyp S R rep Q) {x : Equiv.Perm (Fin 64)}
    (hx : x ∈ hallX1) : ∃ q : ↥Q, phiQ H q = x := by
  obtain ⟨u, huU, e, rfl⟩ := hx
  let q : ↥Q := ⟨rep u * basisProd H e,
    Q.mul_mem ((H.hQV u).mpr huU) (basisProd_mem H e)⟩
  refine ⟨q, ?_⟩
  have hsub : (⟨rep u * basisProd H e, H.hQM q.2⟩ : ↥M) =
      ⟨rep u, rep_mem_M H u⟩ * ⟨basisProd H e, H.hQM (basisProd_mem H e)⟩ := by
    apply Subtype.ext
    rfl
  calc phiQ H q = H.Φ ⟨rep u * basisProd H e, H.hQM q.2⟩ := rfl
    _ = transl u * hallRMPerm e := by rw [hsub, map_mul, phi_rep H u, basisProd_phi]

private lemma hallX1_one (H : Hyp S R rep Q) : (1 : Equiv.Perm (Fin 64)) ∈ hallX1 := by
  refine ⟨0, by decide, 0, ?_⟩
  rw [transl_zero, hallRMPerm_zero H, mul_one]

private lemma xcode_one (H : Hyp S R rep Q) : xcode (1 : Equiv.Perm (Fin 64)) = 0 :=
  (H.hD.xcode_eq_zero 1 (hallX1_one H)).mpr (Or.inl rfl)

private lemma xcode_transl_five (H : Hyp S R rep Q) : xcode (transl 5) = 0 := by
  have hx : transl 5 ∈ hallX1 := by
    refine ⟨5, by decide, 0, ?_⟩
    rw [hallRMPerm_zero H, mul_one]
  exact (H.hD.xcode_eq_zero _ hx).mpr (Or.inr rfl)

private lemma phiQ_inj (H : Hyp S R rep Q) : Function.Injective (phiQ H) := by
  intro q q' h
  have hphi : H.Φ ⟨(q : G), H.hQM q.2⟩ = H.Φ ⟨(q' : G), H.hQM q'.2⟩ := by
    simpa [phiQ_apply] using h
  exact Subtype.ext (congrArg (fun x : ↥M => (x : G)) (H.hΦinj hphi))

private noncomputable def iota (H : Hyp S R rep Q) (q : ↥Q) : Fin 64 :=
  xcode (phiQ H q)

private lemma iota_mul (H : Hyp S R rep Q) (q q' : ↥Q) :
    iota H (q * q') = xorF (iota H q) (iota H q') := by
  simp only [iota, map_mul]
  exact H.hD.xcode_mul _ (phiQ_mem_hallX1 H q) _ (phiQ_mem_hallX1 H q')

private lemma iota_one (H : Hyp S R rep Q) : iota H 1 = 0 := by
  simp only [iota, map_one, xcode_one H]

private lemma phiQ_cQ (H : Hyp S R rep Q) : phiQ H (cQ H) = transl 5 := by
  rw [phiQ_apply]
  exact H.hΦrep ⟨rep 5, H.hQM (rep5_mem_Q H)⟩ 5 rfl

private lemma iota_cQ (H : Hyp S R rep Q) : iota H (cQ H) = 0 := by
  simp only [iota, phiQ_cQ H, xcode_transl_five H]

private lemma xorF_eq_zero_iff {a b : Fin 64} : xorF a b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x => xorF x b) h
    simpa [xorF_assoc, xorF_self, xorF_zero, zero_xorF] using this
  · rintro rfl
    exact xorF_self a

private lemma iota_inv (H : Hyp S R rep Q) (q : ↥Q) : iota H q⁻¹ = iota H q := by
  have h1 : xorF (iota H q) (iota H q⁻¹) = 0 := by
    have h := iota_mul H q q⁻¹
    rw [mul_inv_cancel, iota_one H] at h
    exact h.symm
  exact (xorF_eq_zero_iff.mp h1).symm

private lemma iota_eq_zero_iff (H : Hyp S R rep Q) (q : ↥Q) :
    iota H q = 0 ↔ (q : G) = 1 ∨ (q : G) = rep 5 := by
  have hx := phiQ_mem_hallX1 H q
  rw [iota, H.hD.xcode_eq_zero (phiQ H q) hx]
  constructor
  · rintro (h | h)
    · left
      have hq : q = 1 := phiQ_inj H (by rw [h, map_one])
      rw [hq]
      rfl
    · right
      have hq : q = cQ H := phiQ_inj H (by rw [h, phiQ_cQ H])
      rw [hq, cQ_apply]
  · rintro (h | h)
    · left
      have hq : q = 1 := Subtype.ext h
      rw [hq, map_one]
    · right
      have hq : q = cQ H := Subtype.ext h
      rw [hq, phiQ_cQ H]

private lemma iota_surj (H : Hyp S R rep Q) (k : Fin 64) : ∃ q : ↥Q, iota H q = k := by
  obtain ⟨x, hx, hxk⟩ := H.hD.xcode_surj k
  obtain ⟨q, hq⟩ := exists_phiQ_of_mem_hallX1 H hx
  exact ⟨q, by rw [iota, hq, hxk]⟩

private lemma iota_eq_iff (H : Hyp S R rep Q) (q q' : ↥Q) :
    iota H q = iota H q' ↔ (q' : G) = (q : G) ∨ (q' : G) = (q : G) * rep 5 := by
  constructor
  · intro h
    have h0 : iota H (q' * q⁻¹) = 0 := by
      rw [iota_mul, iota_inv, h, xorF_self]
    rcases (iota_eq_zero_iff H (q' * q⁻¹)).mp h0 with h1 | h5
    · left
      have : (q' * q⁻¹ : ↥Q) = 1 := Subtype.ext h1
      have hq : (q' : G) * (q : G)⁻¹ = 1 := congrArg Subtype.val this
      calc (q' : G) = (q' : G) * (q : G)⁻¹ * (q : G) := by group
        _ = (q : G) := by rw [hq, one_mul]
    · right
      have hq : (q' : G) * (q : G)⁻¹ = rep 5 := h5
      have hq' : (q' : G) = rep 5 * (q : G) := by
        calc (q' : G) = (q' : G) * (q : G)⁻¹ * (q : G) := by group
          _ = rep 5 * (q : G) := by rw [hq]
      rw [hq']
      exact commute_cQ H q
  · rintro (h | h)
    · have hq' : q' = q := Subtype.ext h
      rw [hq']
    · have hq' : q' = q * cQ H := by
        apply Subtype.ext
        change (q' : G) = (q : G) * (cQ H : G)
        rw [h, cQ_apply]
      rw [hq', iota_mul, iota_cQ, xorF_zero]

private noncomputable def sec (H : Hyp S R rep Q) (k : Fin 64) : ↥Q :=
  Classical.choose (iota_surj H k)

private lemma sec_spec (H : Hyp S R rep Q) (k : Fin 64) : iota H (sec H k) = k :=
  Classical.choose_spec (iota_surj H k)

private noncomputable def Ag (H : Hyp S R rep Q) (g : G)
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) : Fin 64 → Fin 64 :=
  fun k => iota H ⟨g * (sec H k : G) * g⁻¹, H.hQn g hg (sec H k) (sec H k).2⟩

private lemma conj_rep5 (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) :
    g * rep 5 * g⁻¹ = rep 5 := by
  have hcomm := Subgroup.mem_centralizer_iff.mp hg (rep 5) (by simp)
  calc g * rep 5 * g⁻¹ = (rep 5 * g) * g⁻¹ := by rw [hcomm]
    _ = rep 5 := by group

private lemma Ag_eq (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) (q : ↥Q) :
    Ag H g hg (iota H q) =
      iota H ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩ := by
  let q' : ↥Q := ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩
  have hsec : iota H q = iota H (sec H (iota H q)) := (sec_spec H (iota H q)).symm
  rcases (iota_eq_iff H q (sec H (iota H q))).mp hsec with h | h
  ·
    have hq : sec H (iota H q) = q := Subtype.ext h
    simp only [Ag, hq]
  ·
    have hq : (sec H (iota H q) : G) = (q : G) * rep 5 := h
    have hconj : (⟨g * (sec H (iota H q) : G) * g⁻¹,
        H.hQn g hg (sec H (iota H q)) (sec H (iota H q)).2⟩ : ↥Q) = q' * cQ H := by
      apply Subtype.ext
      change g * (sec H (iota H q) : G) * g⁻¹ = (g * (q : G) * g⁻¹) * rep 5
      rw [hq]
      calc g * ((q : G) * rep 5) * g⁻¹ = (g * (q : G) * g⁻¹) * (g * rep 5 * g⁻¹) := by
            group
        _ = (g * (q : G) * g⁻¹) * rep 5 := by rw [conj_rep5 H hg]
    simp only [Ag, q']
    rw [hconj, iota_mul, iota_cQ, xorF_zero]

private lemma Ag_mul (H : Hyp S R rep Q) {g g' : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G))
    (hg' : g' ∈ Subgroup.centralizer ({rep 5} : Set G)) :
    Ag H g hg ∘ Ag H g' hg' =
      Ag H (g * g') ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hg hg') := by
  funext k
  let q : ↥Q := ⟨g' * (sec H k : G) * g'⁻¹, H.hQn g' hg' (sec H k) (sec H k).2⟩
  have h1 : Ag H g' hg' k = iota H q := rfl
  have h2 : Ag H (g * g') ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hg hg') k =
      iota H ⟨(g * g') * (sec H k : G) * (g * g')⁻¹,
        H.hQn (g * g') ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hg hg')
          (sec H k) (sec H k).2⟩ := rfl
  rw [Function.comp_apply, h1, h2, Ag_eq H hg q]
  congr 1
  apply Subtype.ext
  change g * (q : G) * g⁻¹ = (g * g') * (sec H k : G) * (g * g')⁻¹
  dsimp [q]
  group

private lemma Ag_mem_hallS40 (H : Hyp S R rep Q) {m : G} (hmM : m ∈ M)
    (hmH : m ∈ Subgroup.centralizer ({rep 5} : Set G)) :
    Ag H m hmH ∈ hallS40 := by
  let s : Equiv.Perm (Fin 64) := S.psiM H.hc ⟨m, hmM⟩
  have hs : s ∈ hexaM := S.psiM_mem_hexaM H.hc ⟨m, hmM⟩
  have hs5 : s 5 = 5 := (S.conj_rep_eq_iff H.hc ⟨m, hmM⟩ 5).mp (conj_rep5 H hmH)
  obtain ⟨b, hb⟩ := H.hΦ ⟨m, hmM⟩
  obtain ⟨σ, hσS40, hσ⟩ := H.hD.xcode_conj b s hs hs5
  have hAg : ∀ k, Ag H m hmH k = σ k := by
    intro k
    let q : ↥Q := sec H k
    have hq : iota H q = k := sec_spec H k
    have hqmem : m * (q : G) * m⁻¹ ∈ Q := H.hQn m hmH (q : G) q.2
    have hsub : (⟨m * (q : G) * m⁻¹, H.hQM hqmem⟩ : ↥M) =
        ⟨m, hmM⟩ * ⟨(q : G), H.hQM q.2⟩ * ⟨m, hmM⟩⁻¹ := by
      apply Subtype.ext
      rfl
    have hΦconj : phiQ H ⟨m * (q : G) * m⁻¹, hqmem⟩ =
        transl b * s * phiQ H q * (transl b * s)⁻¹ := by
      rw [phiQ_apply, hsub]
      simp only [map_mul, map_inv, hb, phiQ_apply]
      dsimp [s]
    calc Ag H m hmH k = iota H ⟨m * (q : G) * m⁻¹, hqmem⟩ := rfl
      _ = xcode (phiQ H ⟨m * (q : G) * m⁻¹, hqmem⟩) := rfl
      _ = xcode (transl b * s * phiQ H q * (transl b * s)⁻¹) := by rw [hΦconj]
      _ = σ (xcode (phiQ H q)) := hσ (phiQ H q) (phiQ_mem_hallX1 H q)
      _ = σ k := by rw [show xcode (phiQ H q) = iota H q from rfl, hq]
  obtain ⟨a, ha, hσa⟩ := hσS40
  refine ⟨a, ha, fun k => ?_⟩
  rw [hAg k, hσa k]

private lemma GoodHall_Ag (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) : GoodHall (Ag H g hg) := by
  by_cases hS : Ag H g hg ∈ hallS40
  · exact Or.inl hS
  · right
    intro p hp hgp
    let q : ↥Q := sec H p
    have hq : iota H q = p := sec_spec H p
    have hp' : IsHallOrb (iota H q) := by rwa [hq]
    obtain ⟨h, hhov, hphi⟩ := H.hD.xcode_orb (phiQ H q) (phiQ_mem_hallX1 H q) hp'
    have hqeq : (q : G) = rep h := by
      have h1 : H.Φ ⟨(q : G), H.hQM q.2⟩ = transl h := by
        simpa [phiQ_apply] using hphi
      have h2 : H.Φ ⟨rep h, rep_mem_M H h⟩ = transl h := phi_rep H h
      exact congrArg (fun x : ↥M => (x : G)) (H.hΦinj (h1.trans h2.symm))
    let q' : ↥Q := ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩
    have hgp' : IsHallOrb (iota H q') := by
      have hp'' : p = iota H q := hq.symm
      rw [hp''] at hgp
      rwa [Ag_eq H hg q] at hgp
    obtain ⟨h', hh'ov, hphi'⟩ := H.hD.xcode_orb (phiQ H q') (phiQ_mem_hallX1 H q') hgp'
    have hconj : g * rep h * g⁻¹ = rep h' := by
      have h1 : H.Φ ⟨(q' : G), H.hQM q'.2⟩ = transl h' := by
        simpa [phiQ_apply] using hphi'
      have h2 : H.Φ ⟨rep h', rep_mem_M H h'⟩ = transl h' := phi_rep H h'
      have hval := congrArg (fun x : ↥M => (x : G)) (H.hΦinj (h1.trans h2.symm))
      simpa [q', hqeq] using hval
    exact hS (Ag_mem_hallS40 H (H.h34 g h h' hhov hh'ov hconj) hg)

private lemma hallS40_surj_Ag (H : Hyp S R rep Q) {σ : Fin 64 → Fin 64}
    (hσ : σ ∈ hallS40) :
    ∃ m : G, ∃ hmM : m ∈ M, ∃ hmH : m ∈ Subgroup.centralizer ({rep 5} : Set G),
      Ag H m hmH = σ := by
  obtain ⟨b, s, hs, hs5, hσeq⟩ := H.hD.xcode_conj_surj σ hσ
  obtain ⟨m', hm'M, hm'H, -, hΦm'⟩ := exists_lift H hs hs5 b
  have hAg : ∀ k, Ag H m' hm'H k = σ k := by
    intro k
    let q : ↥Q := sec H k
    have hq : iota H q = k := sec_spec H k
    have hqmem : m' * (q : G) * m'⁻¹ ∈ Q := H.hQn m' hm'H (q : G) q.2
    have hsub : (⟨m' * (q : G) * m'⁻¹, H.hQM hqmem⟩ : ↥M) =
        ⟨m', hm'M⟩ * ⟨(q : G), H.hQM q.2⟩ * ⟨m', hm'M⟩⁻¹ := by
      apply Subtype.ext
      rfl
    have hΦconj : phiQ H ⟨m' * (q : G) * m'⁻¹, hqmem⟩ =
        transl b * s * phiQ H q * (transl b * s)⁻¹ := by
      rw [phiQ_apply, hsub]
      simp only [map_mul, map_inv, hΦm', phiQ_apply]
    calc Ag H m' hm'H k = iota H ⟨m' * (q : G) * m'⁻¹, hqmem⟩ := rfl
      _ = xcode (phiQ H ⟨m' * (q : G) * m'⁻¹, hqmem⟩) := rfl
      _ = xcode (transl b * s * phiQ H q * (transl b * s)⁻¹) := by rw [hΦconj]
      _ = σ (xcode (phiQ H q)) := hσeq (phiQ H q) (phiQ_mem_hallX1 H q)
      _ = σ k := by rw [show xcode (phiQ H q) = iota H q from rfl, hq]
  exact ⟨m', hm'M, hm'H, funext hAg⟩

private lemma Ag_comp_three (H : Hyp S R rep Q) {g m : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G))
    (hm : m ∈ Subgroup.centralizer ({rep 5} : Set G)) :
    Ag H g hg ∘ Ag H m hm ∘ Ag H g hg =
      Ag H (g * m * g)
        ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem
          ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hg hm) hg) := by
  rw [Ag_mul H hm hg]
  rw [Ag_mul H hg ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hm hg)]
  funext k
  apply congrArg (iota H)
  apply Subtype.ext
  group

private lemma GoodHall_comp_one (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) {t : Fin 64 → Fin 64}
    (ht : t ∈ hallS40) :
    GoodHall (Ag H g hg ∘ t ∘ Ag H g hg) := by
  obtain ⟨m, hmM, hmH, rfl⟩ := hallS40_surj_Ag H ht
  rw [Ag_comp_three H hg hmH]
  exact GoodHall_Ag H ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem
    ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hg hmH) hg)

private lemma GoodHall_comp_two (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) {t u : Fin 64 → Fin 64}
    (ht : t ∈ hallS40) (hu : u ∈ hallS40) :
    GoodHall (Ag H g hg ∘ t ∘ Ag H g hg ∘ u ∘ Ag H g hg) := by
  obtain ⟨m, hmM, hmH, rfl⟩ := hallS40_surj_Ag H ht
  obtain ⟨m', hm'M, hm'H, rfl⟩ := hallS40_surj_Ag H hu
  have hgm : g * m * g ∈ Subgroup.centralizer ({rep 5} : Set G) :=
    (Subgroup.centralizer ({rep 5} : Set G)).mul_mem
      ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hg hmH) hg
  change GoodHall ((Ag H g hg ∘ Ag H m hmH ∘ Ag H g hg) ∘
    (Ag H m' hm'H ∘ Ag H g hg))
  rw [Ag_comp_three H hg hmH]
  rw [Ag_mul H hm'H hg]
  rw [Ag_mul H hgm ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hm'H hg)]
  have hprod : (g * m * g) * (m' * g) ∈ Subgroup.centralizer ({rep 5} : Set G) :=
    (Subgroup.centralizer ({rep 5} : Set G)).mul_mem hgm
      ((Subgroup.centralizer ({rep 5} : Set G)).mul_mem hm'H hg)
  exact GoodHall_Ag H hprod

private lemma Ag_add (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) (k l : Fin 64) :
    Ag H g hg (xorF k l) = xorF (Ag H g hg k) (Ag H g hg l) := by
  obtain ⟨q, rfl⟩ := iota_surj H k
  obtain ⟨q', rfl⟩ := iota_surj H l
  rw [← iota_mul]
  rw [Ag_eq H hg (q * q'), Ag_eq H hg q, Ag_eq H hg q', ← iota_mul]
  congr 1
  apply Subtype.ext
  change g * ((q : G) * (q' : G)) * g⁻¹ =
    (g * (q : G) * g⁻¹) * (g * (q' : G) * g⁻¹)
  group

private lemma Ag_zero (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) {k : Fin 64}
    (hk : Ag H g hg k = 0) : k = 0 := by
  obtain ⟨q, hq⟩ := iota_surj H k
  rw [← hq] at hk
  let q' : ↥Q := ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩
  have hAg : Ag H g hg (iota H q) = iota H q' := Ag_eq H hg q
  have hq'0 : iota H q' = 0 := by rwa [hAg] at hk
  rcases (iota_eq_zero_iff H q').mp hq'0 with h1 | hc
  · have hq1 : (q : G) = 1 := by
      calc (q : G) = g⁻¹ * (q' : G) * g := by dsimp [q']; group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    rw [← hq, (iota_eq_zero_iff H q).mpr (Or.inl hq1)]
  · have hqc : (q : G) = rep 5 := by
      calc (q : G) = g⁻¹ * (q' : G) * g := by dsimp [q']; group
        _ = g⁻¹ * rep 5 * g := by rw [hc]
        _ = rep 5 := by
            simpa using conj_rep5 H ((Subgroup.centralizer ({rep 5} : Set G)).inv_mem hg)
    rw [← hq, (iota_eq_zero_iff H q).mpr (Or.inr hqc)]

private lemma Ag_q0 (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) (k : Fin 64) :
    hallQ0 (Ag H g hg k) = hallQ0 k := by
  obtain ⟨q, rfl⟩ := iota_surj H k
  let q' : ↥Q := ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩
  have hAg : Ag H g hg (iota H q) = iota H q' := Ag_eq H hg q
  rw [hAg]
  have hsq : ∀ r : ↥Q, (phiQ H r * phiQ H r = transl 5) ↔ r * r = cQ H := by
    intro r
    constructor
    · intro h
      have h' : phiQ H (r * r) = phiQ H (cQ H) := by
        rw [map_mul, phiQ_cQ H]
        exact h
      exact phiQ_inj H h'
    · intro h
      rw [← map_mul, h, phiQ_cQ H]
  have hsq_iff : (q' * q' = cQ H) ↔ (q * q = cQ H) := by
    constructor
    · intro h
      apply Subtype.ext
      have hval : (q' : G) * (q' : G) = rep 5 := by
        simpa [cQ_apply] using congrArg (fun x : ↥Q => (x : G)) h
      calc (q : G) * (q : G) = g⁻¹ * ((q' : G) * (q' : G)) * g := by
            dsimp [q']; group
        _ = g⁻¹ * rep 5 * g := by rw [hval]
        _ = rep 5 := by
            simpa using conj_rep5 H ((Subgroup.centralizer ({rep 5} : Set G)).inv_mem hg)
    · intro h
      apply Subtype.ext
      have hval : (q : G) * (q : G) = rep 5 := by
        simpa [cQ_apply] using congrArg (fun x : ↥Q => (x : G)) h
      calc (q' : G) * (q' : G) = g * ((q : G) * (q : G)) * g⁻¹ := by
            dsimp [q']; group
        _ = g * rep 5 * g⁻¹ := by rw [hval]
        _ = rep 5 := conj_rep5 H hg
  apply Bool.eq_iff_iff.mpr
  simp only [iota]
  rw [← H.hD.xcode_sq (phiQ H q') (phiQ_mem_hallX1 H q'),
    ← H.hD.xcode_sq (phiQ H q) (phiQ_mem_hallX1 H q)]
  rw [hsq q', hsq q]
  exact hsq_iff

private lemma reducible_Ag (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) :
    ∀ k, InHallW k → InHallW (Ag H g hg k) :=
  H.hD.reducible (Ag H g hg) (Ag_add H hg) (Ag_q0 H hg) (fun k => Ag_zero H hg)
    (GoodHall_Ag H hg) (fun _ ht => GoodHall_comp_one H hg ht)
    (fun _ ht _ hu => GoodHall_comp_two H hg ht hu)

private lemma inHallW_zero : InHallW (0 : Fin 64) := by decide

private lemma inHallW_xorF {a b : Fin 64} (ha : InHallW a) (hb : InHallW b) :
    InHallW (xorF a b) := by
  revert a b
  decide

private noncomputable def AQ (H : Hyp S R rep Q) : Subgroup ↥Q where
  carrier := {q | InHallW (iota H q)}
  mul_mem' := by
    intro q q' hq hq'
    change InHallW (iota H (q * q'))
    rw [iota_mul]
    exact inHallW_xorF hq hq'
  one_mem' := by
    change InHallW (iota H 1)
    rw [iota_one]
    exact inHallW_zero
  inv_mem' := by
    intro q hq
    change InHallW (iota H q⁻¹)
    rwa [iota_inv]

private noncomputable def A (H : Hyp S R rep Q) : Subgroup G :=
  (AQ H).map Q.subtype

private lemma A_le_Q (H : Hyp S R rep Q) : A H ≤ Q := Subgroup.map_subtype_le _

private lemma c_mem_A (H : Hyp S R rep Q) : rep 5 ∈ A H := by
  rw [A, Subgroup.mem_map]
  refine ⟨cQ H, ?_, rfl⟩
  change InHallW (iota H (cQ H))
  rw [iota_cQ]
  exact inHallW_zero

private lemma iota_fiber_card (H : Hyp S R rep Q) (k : Fin 64) :
    Nat.card {q : ↥Q // iota H q = k} = 2 := by
  let x : {q : ↥Q // iota H q = k} := ⟨sec H k, sec_spec H k⟩
  refine (Nat.card_eq_two_iff' x).mpr ?_
  refine ⟨⟨sec H k * cQ H, ?_⟩, ?_, ?_⟩
  · rw [iota_mul, sec_spec, iota_cQ, xorF_zero]
  · intro h
    have hval : (sec H k : G) * rep 5 = (sec H k : G) := by
      have h' : ((sec H k * cQ H : ↥Q) : G) = ((sec H k : ↥Q) : G) := by
        simpa [x] using congrArg (fun q : {q : ↥Q // iota H q = k} => (q.1 : G)) h
      simpa [cQ_apply] using h'
    have h5 : rep 5 = 1 := by
      have h := congrArg (fun x : G => (sec H k : G)⁻¹ * x) hval
      simpa [mul_assoc] using h
    exact rep5_ne_one H h5
  · intro y hyne
    have hiy : iota H y.1 = iota H (sec H k) := by rw [y.2, sec_spec]
    rcases (iota_eq_iff H (sec H k) y.1).mp hiy.symm with h | h
    · exfalso
      apply hyne
      apply Subtype.ext
      apply Subtype.ext
      simpa [x] using h
    · apply Subtype.ext
      apply Subtype.ext
      change (y.1 : G) = (sec H k : G) * rep 5
      exact h

private noncomputable def AQEquiv (H : Hyp S R rep Q) :
    ↥(AQ H) ≃ Σ k : {k : Fin 64 // InHallW k}, {q : ↥Q // iota H q = k} where
  toFun q := ⟨⟨iota H q.1, q.2⟩, ⟨q.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by
    change InHallW (iota H x.2.1)
    rw [x.2.2]
    exact x.1.2⟩
  left_inv q := rfl
  right_inv x := by
    rcases x with ⟨⟨k, hk⟩, ⟨q, hq⟩⟩
    cases hq
    rfl

private lemma card_AQ (H : Hyp S R rep Q) : Nat.card ↥(AQ H) = 16 := by
  rw [Nat.card_congr (AQEquiv H), Nat.card_sigma]
  simp only [iota_fiber_card]
  rw [Finset.sum_const, Finset.card_univ]
  have hW : Fintype.card {k : Fin 64 // InHallW k} = 8 := by decide
  rw [hW]
  norm_num

private lemma card_A (H : Hyp S R rep Q) : Nat.card (A H) = 16 := by
  rw [A, Subgroup.card_map_of_injective Q.subtype_injective, card_AQ H]

private lemma A_normalized (H : Hyp S R rep Q) {g : G}
    (hg : g ∈ Subgroup.centralizer ({rep 5} : Set G)) {a : G} (ha : a ∈ A H) :
    g * a * g⁻¹ ∈ A H := by
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp ha
  rw [A, Subgroup.mem_map]
  refine ⟨⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩, ?_, rfl⟩
  change InHallW (iota H ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩)
  rw [show iota H ⟨g * (q : G) * g⁻¹, H.hQn g hg (q : G) q.2⟩ =
    Ag H g hg (iota H q) from (Ag_eq H hg q).symm]
  exact reducible_Ag H hg (iota H q) hq

end Hyp

theorem exists_normal_of_split (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (Φ : ↥M →* Equiv.Perm (Fin 64)) (hΦinj : Function.Injective Φ)
    (hΦ : ∀ m : ↥M, ∃ a : Fin 64, Φ m = transl a * S.psiM hc m)
    (hΦrep : ∀ (m : ↥M) (b : Fin 64), (m : G) = rep b → Φ m = transl b)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQc : Q ≤ Subgroup.centralizer ({rep 5} : Set G))
    (hQn : ∀ g ∈ Subgroup.centralizer ({rep 5} : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQV : ∀ v, rep v ∈ Q ↔ InHallU v) (hψQ : S.psiSub hc Q = hallRM)
    (hψM : S.psiSub hc M = hexaM)
    (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = rep 5)
    (hQsq : ∀ a ∈ Q, a * a = 1 ∨ a * a = rep 5)
    (h34 : ∀ (g : G) (h h' : Fin 64), IsOvalVec h → IsOvalVec h' →
      g * rep h * g⁻¹ = rep h' → g ∈ M) :
    ∃ A : Subgroup G, A ≤ Q ∧ rep 5 ∈ A ∧ Nat.card A = 16 ∧
      ∀ g ∈ Subgroup.centralizer ({rep 5} : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
  let H : Hyp S R rep Q :=
    { hF := hF, hD := hD, hc := hc, hC1 := hC1, Φ := Φ, hΦinj := hΦinj,
      hΦ := hΦ, hΦrep := hΦrep, hQM := hQM, hQc := hQc, hQn := hQn,
      hQV := hQV, hψQ := hψQ, hψM := hψM, hQcomm := hQcomm, hQsq := hQsq, h34 := h34 }
  exact ⟨Hyp.A H, Hyp.A_le_Q H, Hyp.c_mem_A H, Hyp.card_A H,
    fun g hg a ha => Hyp.A_normalized H hg ha⟩

end CFSG.CGT.Hall82.Setting

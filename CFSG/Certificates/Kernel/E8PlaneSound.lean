module

public import Certificates.Data.Kernel.E8Plane.Sorted
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksPred
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksGeo
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksWs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksTrip
import CFSG.Certificates.Kernel.E7PlaneKit

public section

namespace CFSG.KC.E8Plane

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

@[expose] def planeKer (b : Fin 2 → Fin Tag.E8.rank → ZMod 3) : Set (Fin Tag.E8.rank → ℤ) :=
  kernelRoots ((triChar (b 0)).prod (triChar (b 1)))

theorem mem_planeKer {b : Fin 2 → Fin Tag.E8.rank → ZMod 3} {α : Fin Tag.E8.rank → ℤ} :
    α ∈ planeKer b ↔ IsRoot Tag.E8 α ∧ triPairing (b 0) α = 0 ∧ triPairing (b 1) α = 0 := by
  simp only [planeKer, kernelRoots, Set.mem_setOf_eq, MonoidHom.prod_apply, Prod.mk_eq_one,
    triChar_apply, Z3.ofAdd_eq_one]

private theorem triPairing_neg' (b : Fin Tag.E8.rank → ZMod 3) (α : Fin Tag.E8.rank → ℤ) :
    triPairing b (-α) = -triPairing b α := by
  simp only [triPairing, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

private theorem neg_mem_planeKer {b : Fin 2 → Fin Tag.E8.rank → ZMod 3}
    {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ planeKer b) : -α ∈ planeKer b := by
  rw [mem_planeKer] at hα ⊢
  exact ⟨IsRoot.neg hα.1, by rw [triPairing_neg', hα.2.1, neg_zero],
    by rw [triPairing_neg', hα.2.2, neg_zero]⟩

theorem image_planeKer {v : WeylGroup Tag.E8} {b : Fin 2 → Fin Tag.E8.rank → ZMod 3}
    (hvb : ∀ s x, triPairing (b s) (v • x) = triPairing (b s) x) :
    (fun α => v • α) '' planeKer b = planeKer b := by
  have hinv : ∀ s x, triPairing (b s) (v⁻¹ • x) = triPairing (b s) x := fun s x => by
    rw [← hvb s (v⁻¹ • x), smul_inv_smul]
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    rw [mem_planeKer] at hβ ⊢
    exact ⟨IsRoot.smul hβ.1 v, by rw [hvb]; exact hβ.2.1, by rw [hvb]; exact hβ.2.2⟩
  · intro hα
    refine ⟨v⁻¹ • α, ?_, smul_inv_smul v α⟩
    rw [mem_planeKer] at hα ⊢
    exact ⟨IsRoot.smul hα.1 v⁻¹, by rw [hinv]; exact hα.2.1, by rw [hinv]; exact hα.2.2⟩

@[expose] def OrthBody (S : Set (Fin Tag.E8.rank → ℤ)) (w : WeylGroup Tag.E8) : Prop :=
  S.ncard = 24 ∧ (∀ γ ∈ S, w • γ = γ ∨ iform γ (w • γ) = 0) ∧
    (∀ d ∈ S, IsOrthTriple w d → ∀ β ∈ S, IsOrthTriple w β →
      ∃ l : List (Fin Tag.E8.rank → ℤ), l.length ≤ 2 ∧ (∀ δ ∈ l, δ ∈ S ∧ IsOrthTriple w δ) ∧
        (l.map (tripleRefl w)).prod • β ∈ ({d, w • d, w ^ 2 • d} : Set (Fin Tag.E8.rank → ℤ))) ∧
    ∃ d ∈ S, iform d (w • d) = 0 ∧ iform d (w ^ 2 • d) = 0 ∧ iform (w • d) (w ^ 2 • d) = 0

@[expose] def E8PlaneOK (v : WeylGroup Tag.E8) (b : Fin 2 → Fin Tag.E8.rank → ZMod 3) : Prop :=
  v ∈ Subgroup.closure (rootReflection '' planeKer b) ∨
    (∃ B : KernelBlocks Tag.E8 (planeKer b),
      ∀ j : Fin 3, (fun α => v • α) '' B.blk j = B.blk (j + 1)) ∨
    ((∀ c : Fin 2 → ZMod 3, c ≠ 0 →
        {α | IsRoot Tag.E8 α ∧ triPairing (c 0 • b 0 + c 1 • b 1) α = 0}.ncard = 78) ∧
      (OrthBody (planeKer b) v ∨ E8D4Triangles v))

@[expose] def ReflTable (rt : Array ℕ) : Prop :=
  ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
    e8Certificate.root (rt.getD (240 * b + x) 0) =
      rootReflection (e8Certificate.root b) • e8Certificate.root x

@[expose] noncomputable def wordR (w : List ℕ) : WeylGroup Tag.E8 :=
  (w.map fun b => rootReflection (e8Certificate.root b)).prod

@[expose] def permA (rt : Array ℕ) (w : List ℕ) : Array ℕ :=
  ((List.range 240).map (e8PlanePermOf rt w)).toArray

@[expose] noncomputable def rtA (RP SP IP : ℕ) : Array ℕ :=
  ((List.range 57600).map fun p => rtF RP SP IP (p / 240) (p % 240)).toArray

theorem permOf8_permA {rt : Array ℕ} (hrt : ReflTable rt) {w : List ℕ} (hw : ∀ b ∈ w, b < 240) :
    PermOf8 (permA rt w) (wordR w) := by
  intro k hk
  rw [permA, toArray_map_range_getD _ _ hk]
  exact e8PlanePermOf_spec hrt hw hk

open CFSG.KC.E7Plane (fld)

private theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl

private theorem nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl

private theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl

private theorem roots_lt32 : ∀ c ∈ e8Certificate.roots, c < 2 ^ 32 := by decide +kernel

private theorem getD_roots_lt {k : ℕ} (hk : k < 240) : e8Certificate.roots.getD k 0 < 2 ^ 32 := by
  rw [List.getD_eq_getElem _ _ (by rw [e8Certificate_roots_length]; exact hk)]
  exact roots_lt32 _ (List.getElem_mem _)

private theorem fld_RP {k : ℕ} (hk : k < 240) :
    fld (pk 32 e8Certificate.roots) 32 k = e8Certificate.roots.getD k 0 := by
  have hk' : k < e8Certificate.roots.length := by rw [e8Certificate_roots_length]; exact hk
  rw [pk, E7Plane.fld_packL (f := fun x => x) roots_lt32 hk', List.getD_eq_getElem _ _ hk']

private theorem sum_E8 {M : Type*} [AddCommMonoid M] (g : Fin Tag.E8.rank → M) :
    ∑ j, g j = g ⟨0, by decide⟩ + g ⟨1, by decide⟩ + g ⟨2, by decide⟩ + g ⟨3, by decide⟩ +
      g ⟨4, by decide⟩ + g ⟨5, by decide⟩ + g ⟨6, by decide⟩ + g ⟨7, by decide⟩ :=
  Fin.sum_univ_eight (M := M) g

private theorem cl_cast (k j : ℕ) (hj : j < 8) :
    ((cl (e8Certificate.roots.getD k 0) j : ℕ) : ℤ) = e8Certificate.root k ⟨j, hj⟩ + 8 := by
  simp only [RootCertificate.root, decodeVec, sub_add_cancel, cl, E7Plane.fld_eq]
  rw [pow_mul]
  norm_num

private theorem code_cast {k : ℕ} (hk : k < 240) :
    ((e8Certificate.roots.getD k 0 : ℕ) : ℤ) =
      ∑ j : Fin Tag.E8.rank, (e8Certificate.root k j + 8) * 16 ^ (j : ℕ) := by
  have hc := getD_roots_lt hk
  rw [sum_E8]
  simp only [RootCertificate.root, decodeVec, sub_add_cancel]
  generalize e8Certificate.roots.getD k 0 = c at hc ⊢
  have h : c = c / 1 % 16 * 1 + c / 16 % 16 * 16 + c / 256 % 16 * 256 + c / 4096 % 16 * 4096 +
      c / 65536 % 16 * 65536 + c / 1048576 % 16 * 1048576 + c / 16777216 % 16 * 16777216 +
      c / 268435456 % 16 * 268435456 := by
    norm_num at hc
    omega
  conv_lhs => rw [h]
  push_cast
  norm_num

private def cN (i j : ℕ) : ℤ :=
  if i = j then 2
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨
      (2 ≤ i ∧ j = i + 1) ∨ (2 ≤ j ∧ i = j + 1) then -1
  else 0

private theorem cartanE8_fact : ∀ p : Fin Tag.E8.rank × Fin Tag.E8.rank,
    Tag.symmetrizedCartan Tag.E8 p.1 p.2 = cN p.1.val p.2.val := by
  decide +kernel

private theorem gramC_cast {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    ((gramC (e8Certificate.roots.getD a 0) (e8Certificate.roots.getD b 0) : ℕ) : ℤ) =
      iform (e8Certificate.root a) (e8Certificate.root b) + 2 := by
  have hn := abs_iform_le_two_of_isRoot_simplyLaced (by tauto) (e8Certificate_isRoot ha)
    (e8Certificate_isRoot hb)
  have hsub : ∀ {A B : ℕ} {z : ℤ}, (A : ℤ) - B = z → 0 ≤ z → ((A - B : ℕ) : ℤ) = z := by
    intro A B z h hz
    omega
  refine hsub ?_ (by linarith [(abs_le.1 hn).1])
  have s8 : ∀ f : ℕ → ℕ, sumN 8 f = 0 + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
    fun _ => rfl
  have s5 : ∀ f : ℕ → ℕ, sumN 5 f = 0 + f 0 + f 1 + f 2 + f 3 + f 4 := fun _ => rfl
  simp only [s8, s5, nat_add_eq, nat_mul_eq]
  push_cast
  simp only [cl_cast a _ (by decide : 0 < 8), cl_cast a _ (by decide : 1 < 8),
    cl_cast a _ (by decide : 2 < 8), cl_cast a _ (by decide : 3 < 8),
    cl_cast a _ (by decide : 4 < 8), cl_cast a _ (by decide : 5 < 8),
    cl_cast a _ (by decide : 6 < 8), cl_cast a _ (by decide : 7 < 8),
    cl_cast b _ (by decide : 0 < 8), cl_cast b _ (by decide : 1 < 8),
    cl_cast b _ (by decide : 2 < 8), cl_cast b _ (by decide : 3 < 8),
    cl_cast b _ (by decide : 4 < 8), cl_cast b _ (by decide : 5 < 8),
    cl_cast b _ (by decide : 6 < 8), cl_cast b _ (by decide : 7 < 8)]
  rw [iform, sum_E8]
  have hBv : ∀ i j : Fin Tag.E8.rank, Tag.symmetrizedCartan Tag.E8 i j = cN i.val j.val :=
    fun i j => cartanE8_fact (i, j)
  simp only [sum_E8, hBv, Fin.val_mk, cN]
  norm_num
  ring

private theorem refl_formula {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β)
    (v : Fin Tag.E8.rank → ℤ) : rootReflection β • v = v - iform β v • β := by
  have h := iform_smul_rootReflection_smul hβ v
  rw [iform_self_eq_two_of_isRoot_simplyLaced (by tauto) hβ] at h
  funext j
  have hj := congrFun h j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hj ⊢
  linarith

private theorem sortB_spec {RP SP IP : ℕ} (hs : sortB RP SP IP = true) :
    (∀ k < 239, fld SP 32 k < fld SP 32 (k + 1)) ∧
      ∀ k < 240, fld IP 8 k < 240 ∧ fld RP 32 (fld IP 8 k) = fld SP 32 k := by
  simp only [sortB, E7Plane.andB_eq, Bool.and_eq_true, E7Plane.allN_eq_true, Nat.blt_eq,
    Nat.beq_eq] at hs
  exact ⟨fun k hk => hs.1 k hk, fun k hk => hs.2 k hk⟩

private theorem fld_lt_of_lt {SP : ℕ} (h : ∀ k < 239, fld SP 32 k < fld SP 32 (k + 1))
    {a b : ℕ} (hab : a < b) (hb : b < 240) : fld SP 32 a < fld SP 32 b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
    · exact (ih h' (by omega)).trans (h b (by omega))
    · exact h a (by omega)

private theorem bstep_spec {SP q p k : ℕ}
    (hm : ∀ a b, a < b → b < 240 → fld SP 32 a < fld SP 32 b) (hq : q < 240)
    (h1 : p ≤ q) (h2 : q < p + 2 * k) :
    bstep SP (fld SP 32 q) k p ≤ q ∧ q < bstep SP (fld SP 32 q) k p + k := by
  rw [bstep, E7Plane.letN_eq]
  cases hc : E7Plane.andB (Nat.blt (Nat.add p k) 240)
    (Nat.ble (fld SP 32 (Nat.add p k)) (fld SP 32 q))
  · change p ≤ q ∧ q < p + k
    refine ⟨h1, ?_⟩
    by_contra hpq
    have h240 : p + k < 240 := by omega
    have hle : fld SP 32 (p + k) ≤ fld SP 32 q := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hpq) with h | h
      · exact (hm _ _ h hq).le
      · rw [h]
    have ht : E7Plane.andB (Nat.blt (Nat.add p k) 240)
        (Nat.ble (fld SP 32 (Nat.add p k)) (fld SP 32 q)) = true := by
      simp only [E7Plane.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, nat_add_eq]
      exact ⟨h240, hle⟩
    rw [hc] at ht
    exact Bool.false_ne_true ht
  · change p + k ≤ q ∧ q < p + k + k
    simp only [E7Plane.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, nat_add_eq] at hc
    refine ⟨?_, by omega⟩
    by_contra hpq
    exact absurd hc.2 (Nat.not_le.2 (hm _ _ (by omega) hc.1))

private theorem bpos_spec {SP q : ℕ} (hm : ∀ a b, a < b → b < 240 → fld SP 32 a < fld SP 32 b)
    (hq : q < 240) : bpos SP (fld SP 32 q) = q := by
  have s := fun k p (h1 : p ≤ q) (h2 : q < p + 2 * k) => bstep_spec (k := k) hm hq h1 h2
  have h128 := s 128 0 (Nat.zero_le _) (by omega)
  have h64 := s 64 _ h128.1 (by omega)
  have h32 := s 32 _ h64.1 (by omega)
  have h16 := s 16 _ h32.1 (by omega)
  have h8 := s 8 _ h16.1 (by omega)
  have h4 := s 4 _ h8.1 (by omega)
  have h2 := s 2 _ h4.1 (by omega)
  have h1 := s 1 _ h2.1 (by omega)
  rw [bpos]
  omega

theorem rtF_sound {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) {b x : ℕ} (hb : b < 240) (hx : x < 240) :
    rtF RP SP IP b x < 240 ∧ e8Certificate.root (rtF RP SP IP b x) =
      rootReflection (e8Certificate.root b) • e8Certificate.root x := by
  obtain ⟨hinc, hI⟩ := sortB_spec hs
  subst hRP
  have hm : ∀ a b, a < b → b < 240 → fld SP 32 a < fld SP 32 b :=
    fun a b hab hb => fld_lt_of_lt hinc hab hb
  have hbR := e8Certificate_isRoot hb
  have hxR := e8Certificate_isRoot hx
  obtain ⟨z, hz, hzv⟩ :=
    e8Certificate_exists_root (IsRoot.smul hxR (rootReflection (e8Certificate.root b)))
  obtain ⟨p, hp, hpz⟩ : ∃ p < 240, fld IP 8 p = z := by
    have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 240)
      (t := Finset.range 240) (fun a _ => fld IP 8 a)
      (fun a ha => Finset.mem_range.2 (hI a (Finset.mem_range.1 ha)).1)
      (fun a₁ a₂ ha₁ ha₂ h => by
        have e : fld SP 32 a₁ = fld SP 32 a₂ := by
          rw [← (hI a₁ (Finset.mem_range.1 ha₁)).2, ← (hI a₂ (Finset.mem_range.1 ha₂)).2, h]
        rcases Nat.lt_trichotomy a₁ a₂ with h' | h' | h'
        · exact absurd e (hm _ _ h' (Finset.mem_range.1 ha₂)).ne
        · exact h'
        · exact absurd e (hm _ _ h' (Finset.mem_range.1 ha₁)).ne')
      le_rfl z (Finset.mem_range.2 hz)
    obtain ⟨a, ha, e⟩ := hsurj
    exact ⟨a, Finset.mem_range.1 ha, e.symm⟩
  have hSp : fld SP 32 p = e8Certificate.roots.getD z 0 := by
    rw [← (hI p hp).2, hpz, fld_RP hz]
  have hcz : ((e8Certificate.roots.getD z 0 : ℕ) : ℤ) =
      (e8Certificate.roots.getD x 0 : ℤ) - iform (e8Certificate.root x) (e8Certificate.root b) *
        ((e8Certificate.roots.getD b 0 : ℤ) - 2290649224) := by
    rw [code_cast hz, code_cast hx, code_cast hb, hzv, refl_formula hbR, iform_comm]
    simp only [sum_E8, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    ring
  have hg := gramC_cast hx hb
  have hn := abs_iform_le_two_of_isRoot_simplyLaced (by tauto) hxR hbR
  have hval : Nat.sub (Nat.add (Nat.add (e8Certificate.roots.getD x 0)
      (Nat.mul (Nat.sub 2 (gramC (e8Certificate.roots.getD x 0) (e8Certificate.roots.getD b 0)))
        (e8Certificate.roots.getD b 0)))
      (Nat.mul (Nat.sub (gramC (e8Certificate.roots.getD x 0) (e8Certificate.roots.getD b 0)) 2)
        2290649224))
      (Nat.add (Nat.mul (Nat.sub (gramC (e8Certificate.roots.getD x 0)
        (e8Certificate.roots.getD b 0)) 2) (e8Certificate.roots.getD b 0))
        (Nat.mul (Nat.sub 2 (gramC (e8Certificate.roots.getD x 0) (e8Certificate.roots.getD b 0)))
          2290649224)) = fld SP 32 p := by
    rw [hSp]
    simp only [nat_add_eq, nat_mul_eq, nat_sub_eq]
    generalize gramC (e8Certificate.roots.getD x 0) (e8Certificate.roots.getD b 0) = g at hg ⊢
    generalize iform (e8Certificate.root x) (e8Certificate.root b) = n at hg hn hcz
    rw [abs_le] at hn
    have hg4 : g ≤ 4 := by omega
    obtain rfl : n = (g : ℤ) - 2 := by omega
    interval_cases g <;> (norm_num at hcz ⊢ <;> omega)
  have hrt : rtF (pk 32 e8Certificate.roots) SP IP b x = z := by
    rw [rtF, E7Plane.letN_eq, E7Plane.letN_eq, E7Plane.letN_eq, fld_RP hx, fld_RP hb, hval,
      bpos_spec hm hp, hpz]
  rw [hrt]
  exact ⟨hz, hzv⟩

theorem reflTable_rtA {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) : ReflTable (rtA RP SP IP) := by
  intro b x hb hx
  have hp : 240 * b + x < 57600 := by omega
  have h1 : (240 * b + x) / 240 = b := by omega
  have h2 : (240 * b + x) % 240 = x := by omega
  rw [rtA, toArray_map_range_getD _ _ hp, h1, h2]
  exact rtF_sound hRP hs hb hx

@[expose] def fixL (P : Array ℕ) : List ℕ :=
  (List.range 6561).filter fun m => e8PlaneFix (((List.range 8).map fun j => P.getD j 0).map
    fun x => (e8PlaneRL ()).getD x []) ((e8PlaneDN ()).getD m [])

@[expose] def sgm (n₀ n₁ : ℕ) : ℕ :=
  (e8PlaneKM (e8PlaneRL ()) (e8PlaneDN ())).getD n₀ 0 &&&
    (e8PlaneKM (e8PlaneRL ()) (e8PlaneDN ())).getD n₁ 0

@[expose] def ElemFacts (rt P : Array ℕ) (ws : List (List ℕ)) : Prop :=
  (ws.all fun w => w.all (fun b => decide (b < 240)) &&
      (List.range 8).map (e8PlanePermOf rt w) == (List.range 8).map fun j => P.getD j 0) = true ∧
    ∀ n₀ ∈ fixL P, ∀ n₁ ∈ fixL P,
      ((ws.map e8PlaneWordMask).any (fun m => sgm n₀ n₁ &&& m == m) ||
        e8PlaneD2 P (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) (sgm n₀ n₁) ||
        (e8PlaneK78 (e8PlaneCnt (e8PlaneRL ()) (e8PlaneDN ())) n₀ n₁ &&
          ((e8PlaneD3 P (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) (sgm n₀ n₁) &&
              e8PlaneD3T rt P (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) (sgm n₀ n₁)) ||
            e8PlaneTri (e8PlaneRL ()) P))) = true

theorem rv_getD {P : Array ℕ} {v : WeylGroup Tag.E8} (hP : PermOf8 P v)
    (j : Fin Tag.E8.rank) :
    (((List.range 8).map fun j => P.getD j 0).map fun x => (e8PlaneRL ()).getD x []).getD j [] =
      List.ofFn (v • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by
  have hj8 : (j : ℕ) < 8 := j.2
  rw [List.getD_eq_getElem _ _ (by simp [hj8]), List.getElem_map, List.getElem_map,
    List.getElem_range]
  obtain ⟨h1, h2⟩ := hP j (by omega)
  rw [e8PlaneRL_getD h1, h2, e8Certificate_root_single]

theorem bool_cases_five {a b c d e : Bool} (h : (a || b || (c && (d || e))) = true) :
    a = true ∨ b = true ∨ (c = true ∧ (d = true ∨ e = true)) := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem planeOK_of_facts {rt P : Array ℕ} (hrt : ReflTable rt) {v : WeylGroup Tag.E8}
    (hP : PermOf8 P v) {ws : List (List ℕ)} (h : ElemFacts rt P ws)
    (b : Fin 2 → Fin Tag.E8.rank → ZMod 3)
    (hvb : ∀ s x, triPairing (b s) (v • x) = triPairing (b s) x) : E8PlaneOK v b := by
  obtain ⟨hws, hF⟩ := h
  choose n hn hnb using fun s => exists_vec3OfIndex (τ := Tag.E8) (b s)
  have hn' : ∀ s, n s < 6561 := fun s => lt_of_lt_of_eq (hn s) (by decide)
  have hmem : ∀ s, n s ∈ fixL P := fun s =>
    List.mem_filter.2 ⟨List.mem_range.2 (hn' s),
      e8PlaneFix_of_mem (hn' s) (rv_getD hP) (by rw [hnb s]; exact hvb s)⟩
  have hσ : sigSet (sgm (n 0) (n 1)) = planeKer b := by
    ext α
    rw [sgm, sigSet_KM_and (hn' 0) (hn' 1), hnb 0, hnb 1, mem_planeKer]
    exact Iff.rfl
  obtain hA | hB | ⟨hK, hD | hT⟩ := bool_cases_five (hF (n 0) (hmem 0) (n 1) (hmem 1))
  · left
    rw [← hσ]
    exact mem_closure_of_any_mask hrt hP hws hA
  · right; left
    obtain ⟨γ, hγ, huniq, hsame, hcyc⟩ := e8PlaneD2_sound hP gramOf8_e8PlaneGram hB
    rw [hσ] at hγ huniq hsame
    exact kernelBlocks_of_gram (S := planeKer b) γ (fun α hα => (mem_planeKer.1 hα).1) hγ
      (fun α hα => neg_mem_planeKer hα) huniq hsame
      (fun α hα δ hδ hαδ => exists_mem_closure_smul_eq_of_iform_ne_zero
        (χ := (triChar (b 0)).prod (triChar (b 1))) hα hδ hαδ)
      (image_planeKer hvb) hcyc
  · right; right
    refine ⟨fun c' hc' => ?_, Or.inl ?_⟩
    · have h78 := e8PlaneK78_spec hK c' hc'
      rwa [hnb 0, hnb 1] at h78
    · obtain ⟨h24, hfix, htr, horb⟩ := e8PlaneD3_full_sound hrt hP gramOf8_e8PlaneGram hD
      rw [hσ] at h24 hfix htr horb
      exact ⟨h24, hfix, htr, horb⟩
  · right; right
    refine ⟨fun c' hc' => ?_, Or.inr (e8PlaneTri_sound hP hT)⟩
    have h78 := e8PlaneK78_spec hK c' hc'
    rwa [hnb 0, hnb 1] at h78

private theorem allL_eq_true {α : Type} {f : α → Bool} :
    ∀ {L : List α}, allL L f = true ↔ ∀ x ∈ L, f x = true
  | [] => ⟨fun _ x hx => by simp at hx, fun _ => rfl⟩
  | x :: L => by
    change E7Plane.andB (f x) (allL L f) = true ↔ _
    rw [E7Plane.andB_eq, Bool.and_eq_true, allL_eq_true]
    simp

private theorem nthL_eq {α : Type} (d : α) : ∀ (L : List α) (i : ℕ), nthL L d i = L.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | x :: L, 0 => by
    rw [List.getD_cons_zero]
    rfl
  | x :: L, i + 1 => by
    rw [List.getD_cons_succ, ← nthL_eq d L i]
    rfl

private theorem table_lt64 : ∀ c ∈ e8Certificate.table, c < 2 ^ 64 := by decide +kernel

private theorem table_length : e8Certificate.table.length = 240 := by decide +kernel

private theorem tb_eq {i y : ℕ} (hi : i < 8) (hy : y < 240) :
    tb (pk 64 e8Certificate.table) i y = e8Certificate.image y ⟨i, hi⟩ := by
  have hy' : y < e8Certificate.table.length := by rw [table_length]; exact hy
  have hT : fld (pk 64 e8Certificate.table) 64 y = e8Certificate.table.getD y 0 := by
    rw [pk, E7Plane.fld_packL (f := fun x => x) table_lt64 hy', List.getD_eq_getElem _ _ hy']
  rw [E7Plane.fld_eq] at hT
  have hm := E7Plane.mod_pow_div_mod (X := pk 64 e8Certificate.table / 2 ^ (64 * y)) (m := 64)
    (k := 8 * i) (w := 8) (by omega)
  have e8 : 8 * (8 * y + i) = 64 * y + 8 * i := by ring
  rw [tb, nat_add_eq, nat_mul_eq, E7Plane.fld_eq, RootCertificate.image, e8, pow_add,
    ← Nat.div_div_eq_div_mul, ← hm, hT]
  simp only [Fin.val_mk]
  rw [pow_mul]
  norm_num

private theorem rt_simple {rt : Array ℕ} (hrt : ReflTable rt) {i y : ℕ} (hi : i < 8)
    (hy : y < 240) : rt.getD (240 * i + y) 0 = tb (pk 64 e8Certificate.table) i y := by
  obtain ⟨h1, h2⟩ := hrt i y (by omega) hy
  have hC := e8Certificate_check
  simp only [RootCertificate.check, Bool.and_eq_true] at hC
  obtain ⟨-, ht⟩ := hC
  simp only [RootCertificate.checkTable, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hy' : y < e8Certificate.roots.length := by rw [e8Certificate_roots_length]; exact hy
  obtain ⟨h3, h4⟩ := ht y hy' ⟨i, hi⟩
  have h4' := RootCertificate.eq_of_ofFn_beq h4
  rw [tb_eq hi hy]
  refine e8Certificate_root_inj h1 (by rwa [e8Certificate_roots_length] at h3) ?_
  have hs : e8Certificate.root i = Pi.single (⟨i, hi⟩ : Fin Tag.E8.rank) 1 :=
    e8Certificate_root_single ⟨i, hi⟩
  rw [h2, h4', hs, rootReflection_eq_conj (w := 1) (one_smul _ _), one_mul, inv_one, mul_one,
    simple_smul]

private theorem actW_eq {rt : Array ℕ} (hrt : ReflTable rt) :
    ∀ (w : List ℕ), (∀ i ∈ w, i < 8) → ∀ {y : ℕ}, y < 240 →
      actW (pk 64 e8Certificate.table) w y = e8PlanePermOf rt w y ∧ e8PlanePermOf rt w y < 240
  | [], _, _, hy => ⟨rfl, hy⟩
  | i :: w, hw, y, hy => by
    obtain ⟨e, hlt⟩ := actW_eq hrt w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) hy
    have hi := hw i List.mem_cons_self
    have e' : actW (pk 64 e8Certificate.table) (i :: w) y =
        tb (pk 64 e8Certificate.table) i (actW (pk 64 e8Certificate.table) w y) := by
      rw [← E7Plane.letN_eq (actW (pk 64 e8Certificate.table) w y)
        (fun z => tb (pk 64 e8Certificate.table) i z)]
      rfl
    have e'' : e8PlanePermOf rt (i :: w) y = rt.getD (240 * i + e8PlanePermOf rt w y) 0 := rfl
    rw [e', e'', e]
    refine ⟨(rt_simple hrt hi hlt).symm, (hrt i _ (by omega) hlt).1⟩

private noncomputable def qRec (T : ℕ) (RW : List (List ℕ)) (v : List ℕ) (x : ℕ × ℕ × List ℕ)
    (c : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (E7Plane.andB (Nat.beq x.1 2) (E7Plane.allN 8 fun j => Nat.beq (actW T v (actW T x.2.2 j))
        (actW T x.2.2 (actW T (nthL RW [] x.2.1) j))))
      (E7Plane.andB (Nat.blt x.2.1 8)
        (E7Plane.notB (Nat.beq (actW T v (actW T v (actW T v x.2.1))) x.2.1)))
      (Nat.beq x.1 1))
    (Nat.beq c 0) (Nat.beq x.1 0)

private theorem qB_walk (T : ℕ) (RW : List (List ℕ)) :
    ∀ (QW : List (List ℕ)) (cj : List (ℕ × ℕ × List ℕ)) (s : ℕ),
      List.rec (motive := fun _ => List (ℕ × ℕ × List ℕ) → ℕ → Bool) (fun _ _ => true)
        (fun v _ ih cj c => List.rec (motive := fun _ => Bool) false (fun x rest _ =>
          E7Plane.andB (qRec T RW v x c) (ih rest (Nat.succ c))) cj) QW cj s = true →
      ∀ c < QW.length, ∃ x ∈ cj, qRec T RW (QW.getD c []) x (s + c) = true
  | [], _, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | _ :: _, [], _, h, _, _ => absurd h Bool.false_ne_true
  | v :: QW, x :: rest, s, h, c, hc => by
    simp only [E7Plane.andB_eq, Bool.and_eq_true] at h
    rcases c with _ | c
    · exact ⟨x, List.mem_cons_self, by simpa using h.1⟩
    · obtain ⟨y, hy, e⟩ := qB_walk T RW QW rest (Nat.succ s) h.2 c
        (by simp only [List.length_cons] at hc; omega)
      refine ⟨y, List.mem_cons_of_mem _ hy, ?_⟩
      have es : s + (c + 1) = Nat.succ s + c := by omega
      rw [List.getD_cons_succ, es]
      exact e

theorem qB_facts {T : ℕ} {QW RW : List (List ℕ)} {CJ : List (ℕ × ℕ × List ℕ)}
    (hT : T = pk 64 e8Certificate.table) (hQW : ∀ w ∈ QW, ∀ i ∈ w, i < 8)
    (hRW : ∀ w ∈ RW, ∀ i ∈ w, i < 8) (hl : lettB CJ = true) (h : qB T QW RW CJ = true)
    {rt : Array ℕ} (hrt : ReflTable rt) (c : ℕ) (hc : c < QW.length) :
    c = 0 ∨
      (∃ x < 8, e8PlanePermOf rt (QW.getD c []) (e8PlanePermOf rt (QW.getD c [])
        (e8PlanePermOf rt (QW.getD c []) x)) ≠ x) ∨
      ∃ i g, (∀ l ∈ g, l < 8) ∧ ∀ j < 8, e8PlanePermOf rt (QW.getD c []) (e8PlanePermOf rt g j) =
        e8PlanePermOf rt g (e8PlanePermOf rt (RW.getD i []) j) := by
  subst hT
  obtain ⟨⟨k, y, g⟩, hx, hr⟩ := qB_walk _ RW QW CJ 0 h c hc
  rw [Nat.zero_add] at hr
  have hv : ∀ i ∈ QW.getD c [], i < 8 := hQW _ (by
    rw [List.getD_eq_getElem _ _ hc]
    exact List.getElem_mem _)
  have hA := fun {y : ℕ} (hy : y < 240) => actW_eq hrt _ hv hy
  by_cases hk0 : k = 0
  · subst hk0
    left
    have e : Nat.beq c 0 = true := hr
    exact Nat.eq_of_beq_eq_true e
  · right
    have hk0' : Nat.beq k 0 = false := by
      cases hb : Nat.beq k 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hk0
    by_cases hk1 : k = 1
    · subst hk1
      left
      have e : E7Plane.andB (Nat.blt y 8) (E7Plane.notB (Nat.beq
          (actW (pk 64 e8Certificate.table) (QW.getD c [])
            (actW (pk 64 e8Certificate.table) (QW.getD c [])
              (actW (pk 64 e8Certificate.table) (QW.getD c []) y))) y)) = true := hr
      simp only [E7Plane.andB_eq, E7Plane.notB_eq, Bool.and_eq_true, Nat.blt_eq,
        Bool.not_eq_true'] at e
      obtain ⟨hy8, hne⟩ := e
      have hne' := Nat.ne_of_beq_eq_false hne
      refine ⟨y, hy8, ?_⟩
      have h1 := hA (y := y) (by omega)
      have h2 := hA h1.2
      have h3 := hA h2.2
      rwa [h1.1, h2.1, h3.1] at hne'
    · right
      have hk1' : Nat.beq k 1 = false := by
        cases hb : Nat.beq k 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hk1
      have e : E7Plane.andB (Nat.beq k 2) (E7Plane.allN 8 fun j =>
          Nat.beq (actW (pk 64 e8Certificate.table) (QW.getD c [])
            (actW (pk 64 e8Certificate.table) g j))
            (actW (pk 64 e8Certificate.table) g
              (actW (pk 64 e8Certificate.table) (nthL RW [] y) j))) = true := by
        simp only [qRec, hk0', hk1'] at hr
        exact hr
      simp only [E7Plane.andB_eq, Bool.and_eq_true, E7Plane.allN_eq_true, Nat.beq_eq,
        nthL_eq] at e
      have hg : ∀ l ∈ g, l < 8 := by
        rw [lettB] at hl
        have := (allL_eq_true.1 hl) _ hx
        simpa [allL_eq_true, Nat.blt_eq] using this
      have hRWy : ∀ l ∈ RW.getD y [], l < 8 := by
        rcases lt_or_ge y RW.length with hy | hy
        · rw [List.getD_eq_getElem _ _ hy]
          exact hRW _ (List.getElem_mem _)
        · rw [List.getD_eq_default _ _ hy]
          simp
      refine ⟨y, g, hg, fun j hj => ?_⟩
      have hj' : j < 240 := by omega
      have a1 := actW_eq hrt g hg hj'
      have a2 := actW_eq hrt (RW.getD y []) hRWy hj'
      have a3 := hA a1.2
      have a4 := actW_eq hrt g hg a2.2
      have ej := e.2 j hj
      rw [a1.1, a3.1, a2.1, a4.1] at ej
      exact ej

private theorem fld_permP {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    {k : ℕ} (hk : k < 240) :
    fld (permP (pk 64 e8Certificate.table) W) 8 k = (permA rt W).getD k 0 := by
  have hf : ∀ i < 240, actW (pk 64 e8Certificate.table) W i < 2 ^ 8 := fun i hi => by
    rw [(actW_eq hrt W hW hi).1]
    exact lt_trans (actW_eq hrt W hW hi).2 (by norm_num)
  rw [E7Plane.fld_eq, permP, E7Plane.orN_digit hf hk, permA, toArray_map_range_getD _ _ hk,
    (actW_eq hrt W hW hk).1]

private theorem rtF_eq_rt {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) {rt : Array ℕ} (hrt : ReflTable rt) {b y : ℕ} (hb : b < 240)
    (hy : y < 240) : rtF RP SP IP b y = rt.getD (240 * b + y) 0 := by
  obtain ⟨h1, h2⟩ := rtF_sound hRP hs hb hy
  obtain ⟨h3, h4⟩ := hrt b y hb hy
  exact e8Certificate_root_inj h1 h3 (h2.trans h4.symm)

private theorem actR_eq {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) {rt : Array ℕ} (hrt : ReflTable rt) :
    ∀ (w : List ℕ), (∀ b ∈ w, b < 240) → ∀ {y : ℕ}, y < 240 →
      actR RP SP IP w y = e8PlanePermOf rt w y ∧ e8PlanePermOf rt w y < 240
  | [], _, _, hy => ⟨rfl, hy⟩
  | b :: w, hw, y, hy => by
    obtain ⟨e, hlt⟩ := actR_eq hRP hs hrt w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) hy
    have hb := hw b List.mem_cons_self
    have e' : actR RP SP IP (b :: w) y = rtF RP SP IP b (actR RP SP IP w y) := by
      rw [← E7Plane.letN_eq (actR RP SP IP w y) (fun z => rtF RP SP IP b z)]
      rfl
    have e'' : e8PlanePermOf rt (b :: w) y = rt.getD (240 * b + e8PlanePermOf rt w y) 0 := rfl
    rw [e', e'', e]
    exact ⟨rtF_eq_rt hRP hs hrt hb hlt, (hrt b _ hb hlt).1⟩

private theorem wordsB_facts {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ}
    (hW : ∀ i ∈ W, i < 8) {WS : List (List ℕ)}
    (h : wordsB RP SP IP (permP (pk 64 e8Certificate.table) W) WS = true) :
    (WS.all fun w => w.all (fun b => decide (b < 240)) &&
      (List.range 8).map (e8PlanePermOf rt w) ==
        (List.range 8).map fun j => (permA rt W).getD j 0) = true ∧
      ∀ w ∈ WS, ∀ b ∈ w, b < 240 := by
  rw [wordsB, allL_eq_true] at h
  have h' : ∀ w ∈ WS, (∀ b ∈ w, b < 240) ∧ ∀ j < 8,
      actR RP SP IP w j = fld (permP (pk 64 e8Certificate.table) W) 8 j := by
    intro w hw
    have hw' := h w hw
    simp only [E7Plane.andB_eq, Bool.and_eq_true, allL_eq_true, Nat.blt_eq, E7Plane.allN_eq_true,
      Nat.beq_eq] at hw'
    exact hw'
  refine ⟨?_, fun w hw => (h' w hw).1⟩
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨hb, hj⟩ := h' w hw
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨fun b hb' => decide_eq_true (hb b hb'), List.map_inj_left.2 fun j hj' => ?_⟩
  have hj8 := List.mem_range.1 hj'
  rw [← (actR_eq hRP hs hrt w hb (by omega)).1, hj j hj8, fld_permP hrt hW (by omega)]

private theorem dg_eq (n i : ℕ) : dg n i = n / 3 ^ i % 3 := rfl

private theorem chv_cast (n k : ℕ) :
    ((chv n (e8Certificate.roots.getD k 0) : ℕ) : ZMod 3) =
      triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root k) := by
  have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
  have hl : ∀ j (hj : j < 8), ((cl (e8Certificate.roots.getD k 0) j : ℕ) : ZMod 3) + 1 =
      ((e8Certificate.root k ⟨j, hj⟩ : ℤ) : ZMod 3) := by
    intro j hj
    have e : ((cl (e8Certificate.roots.getD k 0) j : ℕ) : ℤ) + 1 =
        e8Certificate.root k ⟨j, hj⟩ + 3 * 3 := by
      rw [cl_cast k j hj]
      ring
    have e' := congrArg (Int.cast : ℤ → ZMod 3) e
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_add, Int.cast_mul, h3, zero_mul,
      add_zero] at e'
    exact e'
  have s8 : ∀ f : ℕ → ℕ, sumN 8 f = 0 + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
    fun _ => rfl
  have hm : ∀ a, Nat.mod a 3 = a % 3 := fun _ => rfl
  rw [chv, hm, ZMod.natCast_mod, s8]
  simp only [nat_add_eq, nat_mul_eq, dg_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_zero]
  rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide),
    hl 5 (by decide), hl 6 (by decide), hl 7 (by decide)]
  rw [triPairing, sum_E8]
  simp only [vec3OfIndex, Fin.val_mk]
  ring

private theorem testBit_orN1 {N : ℕ} {f : ℕ → ℕ} (hf : ∀ i < N, f i < 2) {i : ℕ} (hi : i < N) :
    (E7Plane.orN N 1 f).testBit i = true ↔ f i = 1 := by
  rw [E7Plane.testBit_iff_digit]
  have h := E7Plane.orN_digit (w := 1) (f := f) (fun j hj => by
    have := hf j hj
    norm_num
    omega) hi
  rw [one_mul, pow_one] at h
  rw [h]

private theorem toN_eq_one {b : Bool} : E7Plane.toN b = 1 ↔ b = true := by
  cases b <;> decide

private theorem toN_lt (b : Bool) : E7Plane.toN b < 2 := by
  cases b <;> decide

private theorem fixB_of_mem {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ}
    (hW : ∀ i ∈ W, i < 8) {n : ℕ} (hn : n ∈ fixL (permA rt W)) :
    n < 6561 ∧ fixB (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) n = true := by
  rw [fixL, List.mem_filter, List.mem_range] at hn
  obtain ⟨hn, hfix⟩ := hn
  refine ⟨hn, ?_⟩
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  unfold e8PlaneFix at hfix
  rw [List.all_eq_true] at hfix
  rw [fixB, E7Plane.allN_eq_true]
  intro j hj
  have hPj := (hP j (by omega)).1
  have hj' := hfix j (List.mem_range.2 hj)
  have hrv : (((List.range 8).map fun j => (permA rt W).getD j 0).map
      fun x => (e8PlaneRL ()).getD x []).getD j [] =
      List.ofFn (e8Certificate.root ((permA rt W).getD j 0)) := by
    rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_map,
      List.getElem_range, e8PlaneRL_getD hPj]
  rw [decide_eq_true_iff, hrv, e8PlaneDN_getD hn] at hj'
  have h1 := cast_dotL_digits (e8Certificate.root ((permA rt W).getD j 0)) n
  have h3 : (((e8PlaneDigits n).getD j 0 : ℤ) : ZMod 3) = ((dg n j : ℕ) : ZMod 3) := by
    rw [e8PlaneDigits, getD_map_natCast, Int.cast_natCast, digits3,
      List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj)]
    simp [dg_eq]
  have h4 : ((dotL (List.ofFn (e8Certificate.root ((permA rt W).getD j 0))) (e8PlaneDigits n) : ℤ) :
      ZMod 3) = (((e8PlaneDigits n).getD j 0 : ℤ) : ZMod 3) := by
    rw [← sub_eq_zero, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (Int.dvd_of_emod_eq_zero hj')
  rw [h1, h3, ← chv_cast] at h4
  rw [fld_permP hrt hW (by omega), fld_RP hPj, Nat.beq_eq]
  rw [ZMod.natCast_eq_natCast_iff'] at h4
  have hc3 : chv n (e8Certificate.roots.getD ((permA rt W).getD j 0) 0) < 3 :=
    Nat.mod_lt _ (by norm_num)
  have hd3 : dg n j < 3 := Nat.mod_lt _ (by norm_num)
  rwa [Nat.mod_eq_of_lt hc3, Nat.mod_eq_of_lt hd3] at h4

private theorem testBit_fixM {RP P n : ℕ} (hn : n < 6561) :
    (fixM RP P).testBit n = true ↔ fixB RP P n = true := by
  rw [fixM, testBit_orN1 (fun i _ => toN_lt _) hn, toN_eq_one]

private theorem kill_of_nkM {FM b n : ℕ} (hb : b < 240)
    (h0 : Nat.land FM (nkM (pk 32 e8Certificate.roots) b) = 0)
    (hn : n < 6561) (hFM : FM.testBit n = true) :
    triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root b) = 0 := by
  have hbit : (nkM (pk 32 e8Certificate.roots) b).testBit n = false := by
    have := congrArg (fun X => Nat.testBit X n) h0
    simp only [Nat.zero_testBit] at this
    change (FM &&& nkM (pk 32 e8Certificate.roots) b).testBit n = false at this
    rw [Nat.testBit_and, hFM, Bool.true_and] at this
    exact this
  rw [nkM, E7Plane.letN_eq, fld_RP hb] at hbit
  have hc : ¬ (E7Plane.toN (E7Plane.notB (Nat.beq (chv n (e8Certificate.roots.getD b 0)) 0)) = 1) :=
    fun h => by
      have ht := (testBit_orN1 (N := 6561) (f := fun m => E7Plane.toN (E7Plane.notB
        (Nat.beq (chv m (e8Certificate.roots.getD b 0)) 0))) (fun i _ => toN_lt _) hn).2 h
      rw [ht] at hbit
      exact Bool.noConfusion hbit
  rw [toN_eq_one, E7Plane.notB_eq, Bool.not_eq_true', Bool.not_eq_false] at hc
  rw [← chv_cast, Nat.eq_of_beq_eq_true hc, Nat.cast_zero]

private theorem sgm_mask {n₀ n₁ : ℕ} (h0 : n₀ < 6561) (h1 : n₁ < 6561) {w : List ℕ}
    (hw : ∀ b ∈ w, b < 240 ∧ triPairing (vec3OfIndex (τ := .E8) n₀) (e8Certificate.root b) = 0 ∧
      triPairing (vec3OfIndex (τ := .E8) n₁) (e8Certificate.root b) = 0) :
    sgm n₀ n₁ &&& e8PlaneWordMask w = e8PlaneWordMask w := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and, testBit_e8PlaneWordMask]
  by_cases hi : i ∈ w
  · obtain ⟨hi240, hp0, hp1⟩ := hw i hi
    have hs : (sgm n₀ n₁).testBit i = true := by
      rw [sgm, Nat.testBit_and, Bool.and_eq_true, testBit_e8PlaneKM h0, testBit_e8PlaneKM h1]
      exact ⟨⟨hi240, hp0⟩, ⟨hi240, hp1⟩⟩
    rw [hs, Bool.true_and]
  · simp [hi]

theorem easyB_facts {T RP SP IP FM : ℕ} {W : List ℕ} {WS : List (List ℕ)}
    (hT : T = pk 64 e8Certificate.table) (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) (hW : ∀ i ∈ W, i < 8) (hWS : 0 < WS.length)
    (h : easyB RP SP IP (permP T W) FM WS = true) {rt : Array ℕ} (hrt : ReflTable rt) :
    ElemFacts rt (permA rt W) WS := by
  subst hT
  simp only [easyB, E7Plane.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  rw [allL_eq_true] at h
  obtain ⟨hFM, hwords, hkill⟩ := h
  obtain ⟨hws, hlt⟩ := wordsB_facts hRP hs hrt hW hwords
  subst hRP
  refine ⟨hws, fun n₀ hn₀ n₁ hn₁ => ?_⟩
  have hkill' : ∀ n ∈ fixL (permA rt W), ∀ w ∈ WS, ∀ b ∈ w,
      triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root b) = 0 := by
    intro n hn w hw b hb
    obtain ⟨hn', hfix⟩ := fixB_of_mem hrt hW hn
    have hw' := hkill w hw
    rw [allL_eq_true] at hw'
    have hbit : FM.testBit n = true := by
      rw [← hFM]
      exact (testBit_fixM hn').2 hfix
    exact kill_of_nkM (hlt w hw b hb) (Nat.eq_of_beq_eq_true (hw' b hb)) hn' hbit
  have hA : ((WS.map e8PlaneWordMask).any fun m => sgm n₀ n₁ &&& m == m) = true := by
    obtain ⟨w, ws, rfl⟩ : ∃ w ws, WS = w :: ws := by
      cases WS with
      | nil => exact absurd hWS (by simp)
      | cons w ws => exact ⟨w, ws, rfl⟩
    rw [List.any_eq_true]
    refine ⟨e8PlaneWordMask w, List.mem_map_of_mem List.mem_cons_self, beq_iff_eq.2 ?_⟩
    exact sgm_mask (fixB_of_mem hrt hW hn₀).1 (fixB_of_mem hrt hW hn₁).1 fun b hb =>
      ⟨hlt w List.mem_cons_self b hb, hkill' n₀ hn₀ w List.mem_cons_self b hb,
        hkill' n₁ hn₁ w List.mem_cons_self b hb⟩
  rw [hA, Bool.true_or, Bool.true_or]

private theorem anyL_eq_true {α : Type} {f : α → Bool} :
    ∀ {L : List α}, anyL L f = true ↔ ∃ x ∈ L, f x = true
  | [] => ⟨fun h => Bool.noConfusion h, fun ⟨_, hx, _⟩ => by simp at hx⟩
  | x :: L => by
    change E7Plane.orB (f x) (anyL L f) = true ↔ _
    rw [E7Plane.orB_eq, Bool.or_eq_true, anyL_eq_true]
    simp

private theorem testBit_bitsL (n : ℕ) : ∀ L : List ℕ, (bitsL L).testBit n = true ↔ n ∈ L
  | [] => by
    change (0 : ℕ).testBit n = true ↔ n ∈ []
    simp
  | b :: L => by
    have e : bitsL (b :: L) = bitsL L ||| 1 <<< b := rfl
    rw [e, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_bitsL n L, decide_eq_true_iff, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr fun h => Or.inl h.symm, fun h => h.elim (fun h => Or.inr h.symm)
      Or.inl⟩

private theorem wmL_eq : ∀ WS : List (List ℕ), wmL WS = WS.map bitsL
  | [] => rfl
  | w :: WS => by
    rw [List.map_cons, ← wmL_eq WS]
    rfl

private theorem chv_eq_zero_iff (n k : ℕ) : chv n (e8Certificate.roots.getD k 0) = 0 ↔
    triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root k) = 0 := by
  rw [← chv_cast]
  have hc3 : chv n (e8Certificate.roots.getD k 0) < 3 := Nat.mod_lt _ (by norm_num)
  constructor
  · intro h
    rw [h, Nat.cast_zero]
  · intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    omega

private theorem testBit_kmN {n k : ℕ} :
    (kmN (pk 32 e8Certificate.roots) n).testBit k = true ↔
      k < 240 ∧ triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root k) = 0 := by
  by_cases hk : k < 240
  · rw [kmN, testBit_orN1 (fun i _ => toN_lt _) hk, toN_eq_one, Nat.beq_eq, fld_RP hk,
      chv_eq_zero_iff]
    exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  · have hlt : kmN (pk 32 e8Certificate.roots) n < 2 ^ k := by
      rw [kmN]
      exact lt_of_lt_of_le (E7Plane.orN_spec fun i _ => toN_lt _).2
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hlt]
    simp [hk]

private theorem sumN_toN (p : ℕ → Bool) :
    ∀ N, sumN N (fun k => E7Plane.toN (p k)) = ((List.range N).filter p).length
  | 0 => rfl
  | N + 1 => by
    have e : sumN (N + 1) (fun k => E7Plane.toN (p k)) =
        sumN N (fun k => E7Plane.toN (p k)) + E7Plane.toN (p N) := rfl
    rw [e, sumN_toN p N, List.range_succ, List.filter_append, List.length_append]
    cases h : p N <;> simp [List.filter_cons, h, E7Plane.toN_eq]

private theorem pc_kmN {n : ℕ} (hn : n < 6561) :
    pc (kmN (pk 32 e8Certificate.roots) n) =
      (e8PlaneCnt (e8PlaneRL ()) (e8PlaneDN ())).getD n 0 := by
  rw [pc, sumN_toN (fun k => Nat.testBit (kmN (pk 32 e8Certificate.roots) n) k), e8PlaneCnt,
    toArray_map_range_getD _ _ hn]
  refine congrArg List.length (List.filter_congr fun k hk => ?_)
  have hk' := List.mem_range.1 hk
  rw [Bool.eq_iff_iff, testBit_kmN, e8PlaneKill_iff hn hk']
  exact ⟨fun h => h.2, fun h => ⟨hk', h⟩⟩

private noncomputable def sigGo (σ N : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [] (fun k acc =>
    Bool.rec (motive := fun _ => List ℕ) acc (List.cons (Nat.sub 239 k) acc)
      (Nat.testBit σ (Nat.sub 239 k))) N

private theorem brecL (c : Bool) (x y : List ℕ) :
    Bool.rec (motive := fun _ => List ℕ) x y c = if c = true then y else x := by
  cases c <;> rfl

private theorem sigGo_eq (σ : ℕ) : ∀ N, N ≤ 240 →
    sigGo σ N = (List.range' (240 - N) N).filter fun k => σ.testBit k
  | 0, _ => rfl
  | N + 1, hN => by
    have e : sigGo σ (N + 1) = Bool.rec (motive := fun _ => List ℕ) (sigGo σ N)
        ((239 - N) :: sigGo σ N) (σ.testBit (239 - N)) := rfl
    have h1 : 240 - (N + 1) = 239 - N := by omega
    have h2 : 239 - N + 1 = 240 - N := by omega
    rw [e, h1, List.range'_succ, h2, List.filter_cons, sigGo_eq σ N (by omega), brecL]

private theorem sigL_eq (σ : ℕ) : sigL σ = e8PlaneSig σ := by
  have e : sigL σ = sigGo σ 240 := rfl
  rw [e, sigGo_eq σ 240 le_rfl, e8PlaneSig, List.range_eq_range', Nat.sub_self]

private theorem hd_eq (L : List ℕ) : hd L = L.headD 0 := by
  cases L <;> rfl

private theorem gram_cast {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    ((gram (pk 32 e8Certificate.roots) a b : ℕ) : ℤ) =
      (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * a + b) 0 + 2 := by
  rw [gram, fld_RP ha, fld_RP hb, gramC_cast ha hb, e8PlaneGram_getD ha hb]

private theorem gram2_iff {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    gram (pk 32 e8Certificate.roots) a b = 2 ↔
      (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * a + b) 0 = 0 := by
  have := gram_cast ha hb
  omega

private theorem gram4_iff {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    gram (pk 32 e8Certificate.roots) a b ≤ 4 ↔
      (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * a + b) 0 ≤ 2 := by
  have := gram_cast ha hb
  omega

private theorem beq2_eq {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    Nat.beq (gram (pk 32 e8Certificate.roots) a b) 2 =
      ((e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * a + b) 0 == 0) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, gram2_iff ha hb, beq_iff_eq]

private theorem nzB {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    nz (pk 32 e8Certificate.roots) a b =
      ((e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * a + b) 0 != 0) := by
  rw [nz, E7Plane.notB_eq, bne, beq2_eq ha hb]

private theorem orthB_eq {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    {d : ℕ} (hd : d < 240) :
    orthB (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) d =
      ((e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * d + (permA rt W).getD d 0) 0 == 0 &&
        (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD
          (240 * d + (permA rt W).getD ((permA rt W).getD d 0) 0) 0 == 0 &&
        (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD
          (240 * (permA rt W).getD d 0 + (permA rt W).getD ((permA rt W).getD d 0) 0) 0 == 0) := by
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  have h1 := (hP d hd).1
  have h2 := (hP _ h1).1
  simp only [orthB, E7Plane.letB_eq, E7Plane.andB_eq]
  rw [fld_permP hrt hW hd, fld_permP hrt hW h1, beq2_eq hd h1, beq2_eq hd h2, beq2_eq h1 h2,
    Bool.and_assoc]

private noncomputable def tripGo (RP P : ℕ) (L : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun d _ ih =>
    Bool.rec (motive := fun _ => List ℕ) ih (List.cons d ih) (orthB RP P d)) L

private theorem tripGo_eq {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ}
    (hW : ∀ i ∈ W, i < 8) : ∀ L : List ℕ, (∀ d ∈ L, d < 240) →
      tripGo (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) L =
        e8PlaneTrip (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) L
  | [], _ => rfl
  | d :: L, hL => by
    have e : tripGo (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) (d :: L) =
        Bool.rec (motive := fun _ => List ℕ)
          (tripGo (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) L)
          (d :: tripGo (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) L)
          (orthB (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) d) := rfl
    rw [e, orthB_eq hrt hW (hL d List.mem_cons_self),
      tripGo_eq hrt hW L (fun x hx => hL x (List.mem_cons_of_mem _ hx)), brecL, e8PlaneTrip,
      e8PlaneTrip, List.filter_cons]

private theorem tripL_eq {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    (σ : ℕ) : tripL (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) σ =
      e8PlaneTrip (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) (e8PlaneSig σ) := by
  have e : tripL (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) σ =
      tripGo (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) (sigL σ) := rfl
  rw [e, sigL_eq]
  exact tripGo_eq hrt hW _ fun d hd => (mem_e8PlaneSig.1 hd).1

private theorem d2_twin {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    {σ : ℕ} (h : d2B (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) σ = true) :
    e8PlaneD2 (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) σ = true := by
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  have hS : ∀ a ∈ e8PlaneSig σ, a < 240 := fun a ha => (mem_e8PlaneSig.1 ha).1
  have hg0 : (e8PlaneSig σ).headD 0 < 240 := by
    cases hc : e8PlaneSig σ with
    | nil => simp
    | cons x xs => exact hS x (by rw [hc]; exact List.mem_cons_self)
  have hg1 := (hP _ hg0).1
  have hg2 := (hP _ hg1).1
  have hg3 := (hP _ hg2).1
  simp only [d2B, E7Plane.letB_eq, sigL_eq, hd_eq, E7Plane.andB_eq, Bool.and_eq_true,
    allL_eq_true] at h
  rw [fld_permP hrt hW hg0, fld_permP hrt hW hg1, fld_permP hrt hW hg2] at h
  obtain ⟨t0, t1, t2, hcnt, hpair, hlast⟩ := h
  unfold e8PlaneD2
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨t0, t1⟩, t2⟩, fun a ha => ?_⟩, fun a ha b hb => ?_⟩, ?_⟩
  · have e := hcnt a ha
    rw [nzB (hS a ha) hg0, nzB (hS a ha) hg1, nzB (hS a ha) hg2] at e
    simp only [E7Plane.toN_eq, nat_add_eq, Nat.beq_eq] at e
    rw [beq_iff_eq]
    exact e
  · obtain ⟨hrec, hle⟩ := hpair a ha b hb
    have hab := abs_iform_le_two_of_isRoot_simplyLaced (by tauto) (e8Certificate_isRoot (hS a ha))
      (e8Certificate_isRoot (hS b hb))
    rw [← e8PlaneGram_getD (hS a ha) (hS b hb)] at hab
    rw [Nat.ble_eq, gram4_iff (hS a ha) (hS b hb)] at hle
    simp only [blk, nzB (hS a ha) hg0, nzB (hS a ha) hg1, nzB (hS b hb) hg0, nzB (hS b hb) hg1,
      nzB (hS a ha) (hS b hb)] at hrec
    have hy : ∀ A B : ℕ, Nat.beq A B = (A == B) := fun A B => by
      rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
    simp only [hy, E7Plane.notB_eq] at hrec
    refine ⟨⟨?_, decide_eq_true (by linarith [(abs_le.1 hab).1])⟩, decide_eq_true hle⟩
    have br : ∀ (c : Bool) (x y : ℕ), Bool.rec (motive := fun _ => ℕ) x y c =
        if c = true then y else x := fun c x y => by cases c <;> rfl
    have brB : ∀ (c x y : Bool), Bool.rec (motive := fun _ => Bool) x y c =
        if c = true then y else x := fun c x y => by cases c <;> rfl
    simp only [br, brB] at hrec
    revert hrec
    split_ifs <;> simp_all
  · rw [nzB hg3 hg0] at hlast
    exact hlast

private theorem d3_twin {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    {σ : ℕ} (h : d3B (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) σ = true) :
    e8PlaneD3 (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) σ = true := by
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  have hS : ∀ a ∈ e8PlaneSig σ, a < 240 := fun a ha => (mem_e8PlaneSig.1 ha).1
  simp only [d3B, sigL_eq, E7Plane.andB_eq, E7Plane.orB_eq, Bool.and_eq_true, allL_eq_true,
    anyL_eq_true, Bool.or_eq_true, Nat.beq_eq, E7Plane.lenL_eq] at h
  obtain ⟨hlen, hall, d, hd, horth⟩ := h
  unfold e8PlaneD3
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨hlen, fun g hg => ?_⟩, d, hd, ?_⟩
  · have e0 := hall g hg
    rw [fld_permP hrt hW (hS g hg)] at e0
    rcases e0 with e | e
    · exact Or.inl e
    · exact Or.inr ((gram2_iff (hS g hg) (hP _ (hS g hg)).1).1 e)
  · rw [orthB_eq hrt hW (hS d hd)] at horth
    simpa only [Bool.and_eq_true, beq_iff_eq] using horth

private theorem allIL_exists {α : Type} {f : ℕ → α → Bool} :
    ∀ (L : List α) (s : ℕ), allIL L f s = true → ∀ x ∈ L, ∃ i, f i x = true
  | [], _, _, x, hx => by simp at hx
  | y :: L, s, h, x, hx => by
    have e : allIL (y :: L) f s =
        E7Plane.letB s (fun i => E7Plane.andB (f i y) (allIL L f (Nat.succ i))) := rfl
    simp only [e, E7Plane.letB_eq, E7Plane.andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨s, h.1⟩
    · exact allIL_exists L _ h.2 x hx

private theorem trF_eq {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ}
    (hW : ∀ i ∈ W, i < 8) {δ x : ℕ} (hδ : δ < 240) (hx : x < 240) :
    trF RP SP IP (permP (pk 64 e8Certificate.table) W) δ x = e8PlaneTR rt (permA rt W) δ x ∧
      e8PlaneTR rt (permA rt W) δ x < 240 := by
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  have h1 := (hP δ hδ).1
  have h2 := (hP _ h1).1
  have hw : ∀ b ∈ [δ, (permA rt W).getD δ 0, (permA rt W).getD ((permA rt W).getD δ 0) 0],
      b < 240 := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> assumption
  obtain ⟨e, hlt⟩ := actR_eq hRP hs hrt _ hw hx
  refine ⟨?_, hlt⟩
  rw [e8PlaneTR, ← e]
  simp only [trF, E7Plane.letN_eq]
  rw [fld_permP hrt hW hδ, fld_permP hrt hW h1]
  simp only [actR, E7Plane.letN_eq]

private theorem d3t_twin {RP SP IP : ℕ} (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ}
    (hW : ∀ i ∈ W, i < 8) {σ : ℕ} (hσ : σ < 2 ^ 240) {ws : List ℕ}
    (h : d3tB RP SP IP (permP (pk 64 e8Certificate.table) W) σ ws = true) :
    e8PlaneD3T rt (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) σ = true := by
  subst hRP
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  have hT : ∀ d ∈ e8PlaneTrip (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ()))
      (e8PlaneSig σ), d < 240 := fun d hd =>
    (mem_e8PlaneSig.1 (List.mem_of_mem_filter hd)).1
  have hinT : ∀ δ,
      inT (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) σ δ = true →
      δ ∈ e8PlaneTrip (permA rt W) (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) (e8PlaneSig σ) := by
    intro δ e
    rw [inT, E7Plane.andB_eq, Bool.and_eq_true] at e
    have hδ : δ < 240 := by
      by_contra hδ
      have := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hσ
        (Nat.pow_le_pow_right (by norm_num) (by omega : 240 ≤ δ)))
      rw [this] at e
      exact Bool.noConfusion e.1
    rw [orthB_eq hrt hW hδ] at e
    rw [e8PlaneTrip, List.mem_filter, mem_e8PlaneSig]
    exact ⟨⟨hδ, e.1⟩, e.2⟩
  have hTgt : ∀ d x, d < 240 → inTgt (permP (pk 64 e8Certificate.table) W) d x = true →
      [d, (permA rt W).getD d 0, (permA rt W).getD ((permA rt W).getD d 0) 0].contains x =
        true := by
    intro d x hd e
    rw [inTgt, fld_permP hrt hW hd, fld_permP hrt hW (hP d hd).1] at e
    simp only [E7Plane.orB_eq, Bool.or_eq_true, Nat.beq_eq] at e
    rw [List.contains_iff_mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact e
  simp only [d3tB, E7Plane.letB_eq] at h
  rw [tripL_eq hrt hW] at h
  unfold e8PlaneD3T
  simp only [List.all_eq_true, Bool.or_eq_true, List.any_eq_true]
  intro d hd β hβ
  obtain ⟨i, hi⟩ := allIL_exists _ 0 h d hd
  obtain ⟨c, hc⟩ : ∃ c, witB (pk 32 e8Certificate.roots) SP IP
      (permP (pk 64 e8Certificate.table) W) σ d β c = true := by
    obtain ⟨j, hj⟩ := allIL_exists _ 0 hi β hβ
    exact ⟨_, hj⟩
  have hd' := hT d hd
  have hβ' := hT β hβ
  unfold witB at hc
  cases hc0 : Nat.beq c 0
  · rw [hc0] at hc
    cases hc1 : Nat.blt c 256
    · rw [hc1] at hc
      simp only [E7Plane.letB_eq, E7Plane.andB_eq, Bool.and_eq_true] at hc
      obtain ⟨h1, h2, h3⟩ := hc
      have m1 := hinT _ h1
      have m2 := hinT _ h2
      obtain ⟨e2, l2⟩ := trF_eq rfl hs hrt hW (hT _ m2) hβ'
      rw [e2] at h3
      obtain ⟨e1, -⟩ := trF_eq rfl hs hrt hW (hT _ m1) l2
      rw [e1] at h3
      exact Or.inr ⟨_, m1, _, m2, hTgt d _ hd' h3⟩
    · rw [hc1] at hc
      simp only [E7Plane.andB_eq, Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc
      have m1 := hinT _ h1
      obtain ⟨e1, -⟩ := trF_eq rfl hs hrt hW (hT _ m1) hβ'
      rw [e1] at h2
      exact Or.inl (Or.inr ⟨_, m1, hTgt d _ hd' h2⟩)
  · rw [hc0] at hc
    exact Or.inl (Or.inl (hTgt d β hd' hc))

private theorem kmL_eq (RP : ℕ) : ∀ FL : List ℕ, kmL RP FL = FL.map fun n => (n, kmN RP n)
  | [] => rfl
  | n :: FL => by
    rw [List.map_cons, ← kmL_eq RP FL]
    rfl

private theorem fstL_eq : ∀ L : List (ℕ × List ℕ), fstL L = L.map Prod.fst
  | [] => rfl
  | x :: L => by
    rw [List.map_cons, ← fstL_eq L]
    rfl

private theorem memL_iff {L : List ℕ} {x : ℕ} : memL L x = true ↔ x ∈ L := by
  rw [memL, anyL_eq_true]
  simp only [Nat.beq_eq, exists_eq_right]

private theorem kmN_eq {n : ℕ} (hn : n < 6561) :
    kmN (pk 32 e8Certificate.roots) n = (e8PlaneKM (e8PlaneRL ()) (e8PlaneDN ())).getD n 0 :=
  Nat.eq_of_testBit_eq fun k => Bool.eq_iff_iff.2 (by rw [testBit_kmN, testBit_e8PlaneKM hn])

private theorem kmN_lt (n : ℕ) : kmN (pk 32 e8Certificate.roots) n < 2 ^ 240 := by
  rw [kmN]
  exact (E7Plane.orN_spec fun i _ => toN_lt _).2

private theorem combo_eq (n₀ n₁ c₀ c₁ : ℕ) : combo n₀ n₁ c₀ c₁ = e8PlaneCombo n₀ n₁ c₀ c₁ := by
  rw [e8PlaneCombo_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

private theorem fld_or (A B n : ℕ) : fld (A ||| B) 8 n = fld A 8 n ||| fld B 8 n := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  simp only [E7Plane.fld_eq, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  cases decide (k < 8) <;> simp

private theorem fld_shift (v q n : ℕ) (hv : v < 256) :
    fld (v <<< (8 * q)) 8 n = if q = n then v else 0 := by
  rw [E7Plane.fld_eq, Nat.shiftLeft_eq]
  rcases lt_trichotomy q n with h | rfl | h
  · rw [if_neg h.ne, Nat.div_eq_of_lt, Nat.zero_mod]
    have h2 : 0 < 2 ^ (8 * q) := by positivity
    have h3 : v * 2 ^ (8 * q) < 256 * 2 ^ (8 * q) := by nlinarith
    have h4 : 256 * 2 ^ (8 * q) = 2 ^ (8 * q + 8) := by
      rw [pow_add]
      ring
    have h5 : 2 ^ (8 * q + 8) ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (h3.trans_eq h4) h5
  · rw [if_pos rfl, Nat.mul_div_cancel _ (by positivity), Nat.mod_eq_of_lt (by norm_num; omega)]
  · have e : v * 2 ^ (8 * q) = v * 2 ^ (8 * (q - n - 1)) * 2 ^ 8 * 2 ^ (8 * n) := by
      rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [if_neg h.ne', e, Nat.mul_div_cancel _ (by positivity), Nat.mul_mod_left]

private theorem nat_mod_eq' (a b : ℕ) : Nat.mod a b = a % b := rfl

private theorem nat_div_eq' (a b : ℕ) : Nat.div a b = a / b := rfl

private theorem wordMask_eq (w : List ℕ) : e8PlaneWordMask w = bitsL w :=
  Nat.eq_of_testBit_eq fun n => Bool.eq_iff_iff.2 (by
    rw [testBit_e8PlaneWordMask, decide_eq_true_iff, testBit_bitsL])

private theorem fld_cntP {FC : List ℕ}
    (hFC : ∀ x ∈ FC, pc (kmN (pk 32 e8Certificate.roots) (x / 256)) = x % 256) (n : ℕ) :
    fld (cntP FC) 8 n = 0 ∨ fld (cntP FC) 8 n = pc (kmN (pk 32 e8Certificate.roots) n) := by
  induction FC with
  | nil =>
    left
    change fld 0 8 n = 0
    rw [E7Plane.fld_eq, Nat.zero_div, Nat.zero_mod]
  | cons x FC ih =>
    have e : cntP (x :: FC) = cntP FC ||| (x % 256) <<< (8 * (x / 256)) := rfl
    rw [e, fld_or, fld_shift _ _ _ (Nat.mod_lt _ (by norm_num))]
    rcases ih fun y hy => hFC y (List.mem_cons_of_mem _ hy) with h | h <;> rw [h] <;>
      by_cases hq : x / 256 = n
    · rw [if_pos hq, ← hFC x List.mem_cons_self, hq, Nat.zero_or]
      exact Or.inr rfl
    · rw [if_neg hq, Nat.or_zero]
      exact Or.inl rfl
    · rw [if_pos hq, ← hFC x List.mem_cons_self, hq, Nat.or_self]
      exact Or.inr rfl
    · rw [if_neg hq, Nat.or_zero]
      exact Or.inr rfl

private theorem k78_twin {FC : List ℕ}
    (hFC : ∀ x ∈ FC, pc (kmN (pk 32 e8Certificate.roots) (x / 256)) = x % 256) {n₀ n₁ : ℕ}
    (h : k78 (cntP FC) n₀ n₁ = true) :
    e8PlaneK78 (e8PlaneCnt (e8PlaneRL ()) (e8PlaneDN ())) n₀ n₁ = true := by
  rw [k78, E7Plane.allN_eq_true] at h
  unfold e8PlaneK78
  rw [List.all_eq_true]
  intro c hc
  have e := h c (List.mem_range.1 hc)
  simp only [Nat.beq_eq, nat_mod_eq', nat_div_eq', nat_add_eq, combo_eq] at e
  have hlt := e8PlaneCombo_lt n₀ n₁ ((c + 1) % 3) ((c + 1) / 3)
  rcases fld_cntP hFC (e8PlaneCombo n₀ n₁ ((c + 1) % 3) ((c + 1) / 3)) with h0 | h0
  · rw [h0] at e
    exact absurd e (by norm_num)
  · rw [h0, pc_kmN hlt] at e
    exact beq_iff_eq.2 e

private theorem fixB_iff {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    {n : ℕ} : fixB (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W) n = true ↔
      ∀ j (hj : j < 8), triPairing (vec3OfIndex (τ := .E8) n)
        (e8Certificate.root ((permA rt W).getD j 0)) = vec3OfIndex (τ := .E8) n ⟨j, hj⟩ := by
  rw [fixB, E7Plane.allN_eq_true]
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  refine forall_congr' fun j => ⟨fun h hj => ?_, fun h hj => ?_⟩
  · have e := h hj
    rw [fld_permP hrt hW (by omega), fld_RP (hP j (by omega)).1, Nat.beq_eq] at e
    rw [← chv_cast, e]
    rfl
  · rw [fld_permP hrt hW (by omega), fld_RP (hP j (by omega)).1, Nat.beq_eq]
    have e : ((chv n (e8Certificate.roots.getD ((permA rt W).getD j 0) 0) : ℕ) : ZMod 3) =
        ((dg n j : ℕ) : ZMod 3) := by
      rw [chv_cast]
      exact h hj
    have hc3 : chv n (e8Certificate.roots.getD ((permA rt W).getD j 0) 0) < 3 :=
      Nat.mod_lt _ (by norm_num)
    have hd3 : dg n j < 3 := Nat.mod_lt _ (by norm_num)
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc3, Nat.mod_eq_of_lt hd3] at e

private theorem mem_FL {RP P FM : ℕ} {FL : List ℕ} (hFM : fixM RP P = FM) (hb : bitsL FL = FM)
    {n : ℕ} (hn : n < 6561) (hf : fixB RP P n = true) : n ∈ FL := by
  rw [← testBit_bitsL, hb, ← hFM]
  exact (testBit_fixM hn).2 hf

private theorem triPairing_comb' (c₀ c₁ : ZMod 3) (b₀ b₁ : Fin Tag.E8.rank → ZMod 3)
    (v : Fin Tag.E8.rank → ℤ) :
    triPairing (c₀ • b₀ + c₁ • b₁) v = c₀ * triPairing b₀ v + c₁ * triPairing b₁ v := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

private theorem tri_of {rt : Array ℕ} (hrt : ReflTable rt) {W : List ℕ} (hW : ∀ i ∈ W, i < 8)
    (hnf : ∀ r < 240, fld (permP (pk 64 e8Certificate.table) W) 8 r ≠ r)
    (htr : sumN 8 (fun j => cl (fld (pk 32 e8Certificate.roots) 32
      (fld (permP (pk 64 e8Certificate.table) W) 8 j)) j) = 60) :
    e8PlaneTri (e8PlaneRL ()) (permA rt W) = true := by
  have hP := permOf8_permA hrt (w := W) fun b hb => lt_trans (hW b hb) (by norm_num)
  unfold e8PlaneTri
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  constructor
  · intro r hr
    have hr' := List.mem_range.1 hr
    rw [e8PlaneRL_getD (hP r hr').1, e8PlaneRL_getD hr', bne_iff_ne, ne_eq]
    intro e
    apply hnf r hr'
    rw [fld_permP hrt hW hr']
    exact e8Certificate_root_inj (hP r hr').1 hr' (List.ofFn_injective e)
  · have hg : ∀ j (hj : j < 8), ((e8PlaneRL ()).getD ((permA rt W).getD j 0) []).getD j 0 =
        e8Certificate.root ((permA rt W).getD j 0) ⟨j, hj⟩ := fun j hj => by
      rw [e8PlaneRL_getD (hP j (by omega)).1]
      exact getD_ofFn_eq _ ⟨j, hj⟩
    have hl : ∀ j (hj : j < 8), ((cl (fld (pk 32 e8Certificate.roots) 32
        (fld (permP (pk 64 e8Certificate.table) W) 8 j)) j : ℕ) : ℤ) =
        e8Certificate.root ((permA rt W).getD j 0) ⟨j, hj⟩ + 8 := fun j hj => by
      rw [fld_permP hrt hW (by omega), fld_RP (hP j (by omega)).1, cl_cast _ j hj]
    have s8 : ∀ f : ℕ → ℕ, sumN 8 f = 0 + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
      fun _ => rfl
    have htr' := congrArg (Nat.cast : ℕ → ℤ) htr
    rw [s8] at htr'
    simp only [nat_add_eq, Nat.cast_add, Nat.cast_zero, Nat.cast_ofNat] at htr'
    rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide),
      hl 5 (by decide), hl 6 (by decide), hl 7 (by decide)] at htr'
    rw [foldr_range_add, add_zero]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide), hg 3 (by decide), hg 4 (by decide),
      hg 5 (by decide), hg 6 (by decide), hg 7 (by decide)]
    linarith

theorem rep4B_facts {T RP SP IP FM : ℕ} {W : List ℕ} {FL : List ℕ} {WS : List (List ℕ)}
    (hT : T = pk 64 e8Certificate.table) (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) (hW : ∀ i ∈ W, i < 8)
    (h : rep4B RP SP IP (permP T W) FM FL WS = true) {rt : Array ℕ} (hrt : ReflTable rt) :
    ElemFacts rt (permA rt W) WS := by
  subst hT
  simp only [rep4B, fixB', E7Plane.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hFM, hbits, -, hwords⟩, hFL, hnofix, htr⟩ := h
  obtain ⟨hws, hlt⟩ := wordsB_facts hRP hs hrt hW hwords
  subst hRP
  rw [allL_eq_true] at hFL
  rw [E7Plane.allN_eq_true] at hnofix
  have hFL' : ∀ n ∈ FL, (n = 0 ∨ pc (kmN (pk 32 e8Certificate.roots) n) = 78) ∧
      ∃ w ∈ WS, ∀ b ∈ w, b < 240 ∧
        triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root b) = 0 := by
    intro n hn
    have e := hFL n hn
    simp only [E7Plane.letB_eq, E7Plane.andB_eq, E7Plane.orB_eq, Bool.and_eq_true,
      Bool.or_eq_true, Nat.beq_eq, anyL_eq_true] at e
    obtain ⟨h78, m, hmW, hm⟩ := e
    rw [wmL_eq, List.mem_map] at hmW
    obtain ⟨w, hw, rfl⟩ := hmW
    refine ⟨h78, w, hw, fun b hb => ⟨hlt w hw b hb, ?_⟩⟩
    have hbit : (bitsL w).testBit b = true := (testBit_bitsL b w).2 hb
    rw [← hm] at hbit
    change (kmN (pk 32 e8Certificate.roots) n &&& bitsL w).testBit b = true at hbit
    rw [Nat.testBit_and, Bool.and_eq_true] at hbit
    exact (testBit_kmN.1 hbit.1).2
  refine ⟨hws, fun n₀ hn₀ n₁ hn₁ => ?_⟩
  obtain ⟨h0, hf0⟩ := fixB_of_mem hrt hW hn₀
  obtain ⟨h1, hf1⟩ := fixB_of_mem hrt hW hn₁
  have hA : ∀ w ∈ WS, (∀ b ∈ w, b < 240 ∧
      triPairing (vec3OfIndex (τ := .E8) n₀) (e8Certificate.root b) = 0 ∧
      triPairing (vec3OfIndex (τ := .E8) n₁) (e8Certificate.root b) = 0) →
      ((WS.map e8PlaneWordMask).any fun m => sgm n₀ n₁ &&& m == m) = true := fun w hw hb => by
    rw [List.any_eq_true]
    exact ⟨_, List.mem_map_of_mem hw, beq_iff_eq.2 (sgm_mask h0 h1 hb)⟩
  by_cases h01 : ∀ k < 240, triPairing (vec3OfIndex (τ := .E8) n₀) (e8Certificate.root k) = 0 →
      triPairing (vec3OfIndex (τ := .E8) n₁) (e8Certificate.root k) = 0
  · obtain ⟨-, w, hw, hwb⟩ := hFL' n₀ (mem_FL hFM hbits h0 hf0)
    rw [hA w hw fun b hb => ⟨(hwb b hb).1, (hwb b hb).2, h01 b (hwb b hb).1 (hwb b hb).2⟩,
      Bool.true_or, Bool.true_or]
  by_cases h10 : ∀ k < 240, triPairing (vec3OfIndex (τ := .E8) n₁) (e8Certificate.root k) = 0 →
      triPairing (vec3OfIndex (τ := .E8) n₀) (e8Certificate.root k) = 0
  · obtain ⟨-, w, hw, hwb⟩ := hFL' n₁ (mem_FL hFM hbits h1 hf1)
    rw [hA w hw fun b hb => ⟨(hwb b hb).1, h10 b (hwb b hb).1 (hwb b hb).2, (hwb b hb).2⟩,
      Bool.true_or, Bool.true_or]
  push Not at h01 h10
  obtain ⟨k, hk, hk0, hk1⟩ := h01
  obtain ⟨k', hk', hk'1, hk'0⟩ := h10
  have hK : e8PlaneK78 (e8PlaneCnt (e8PlaneRL ()) (e8PlaneDN ())) n₀ n₁ = true := by
    unfold e8PlaneK78
    rw [List.all_eq_true]
    intro c hc
    have hc8 := List.mem_range.1 hc
    have hlt' := e8PlaneCombo_lt n₀ n₁ ((c + 1) % 3) ((c + 1) / 3)
    have hv := vec3OfIndex_e8PlaneCombo n₀ n₁ ((c + 1) % 3) ((c + 1) / 3)
    have hfix : fixB (pk 32 e8Certificate.roots) (permP (pk 64 e8Certificate.table) W)
        (e8PlaneCombo n₀ n₁ ((c + 1) % 3) ((c + 1) / 3)) = true := by
      rw [fixB_iff hrt hW]
      intro j hj
      rw [hv, triPairing_comb', (fixB_iff hrt hW).1 hf0 j hj, (fixB_iff hrt hW).1 hf1 j hj]
      rfl
    have hne : e8PlaneCombo n₀ n₁ ((c + 1) % 3) ((c + 1) / 3) ≠ 0 := by
      intro hz
      have hz' : ((((c + 1) % 3 : ℕ) : ZMod 3) • vec3OfIndex (τ := .E8) n₀ +
          (((c + 1) / 3 : ℕ) : ZMod 3) • vec3OfIndex (τ := .E8) n₁) = 0 := by
        rw [← hv, hz]
        funext j
        simp [vec3OfIndex]
      have t1 := congrArg (fun b => triPairing b (e8Certificate.root k)) hz'
      have t2 := congrArg (fun b => triPairing b (e8Certificate.root k')) hz'
      simp only [triPairing_comb', hk0, hk'1, mul_zero, zero_add, add_zero] at t1 t2
      have z0 : triPairing (0 : Fin Tag.E8.rank → ZMod 3) (e8Certificate.root k) = 0 := by
        simp [triPairing]
      have z0' : triPairing (0 : Fin Tag.E8.rank → ZMod 3) (e8Certificate.root k') = 0 := by
        simp [triPairing]
      rw [z0] at t1
      rw [z0'] at t2
      have c1 := (mul_eq_zero.1 t1).resolve_right hk1
      have c0 := (mul_eq_zero.1 t2).resolve_right hk'0
      rw [ZMod.natCast_eq_zero_iff] at c0 c1
      omega
    obtain ⟨h78, -⟩ := hFL' _ (mem_FL hFM hbits hlt' hfix)
    exact beq_iff_eq.2 ((pc_kmN hlt').symm.trans (h78.resolve_left hne))
  have hT := tri_of hrt hW (fun r hr => by
    have e := hnofix r hr
    rw [E7Plane.notB_eq, Bool.not_eq_true'] at e
    exact Nat.ne_of_beq_eq_false e) htr
  rw [hK, hT, Bool.or_true, Bool.true_and, Bool.or_true]

theorem rep3B_facts {T RP SP IP FM : ℕ} {W : List ℕ} {FL FC : List ℕ} {WS : List (List ℕ)}
    {D2 : List ℕ} {D3 : List (ℕ × List ℕ)}
    (hT : T = pk 64 e8Certificate.table) (hRP : RP = pk 32 e8Certificate.roots)
    (hs : sortB RP SP IP = true) (hW : ∀ i ∈ W, i < 8)
    (h : rep3B RP SP IP (permP T W) FM FL FC WS D2 D3 = true) {rt : Array ℕ}
    (hrt : ReflTable rt) : ElemFacts rt (permA rt W) WS := by
  subst hT
  simp only [rep3B, fixB', pairsB, excB, E7Plane.andB_eq, E7Plane.letB_eq, Bool.and_eq_true,
    Nat.beq_eq] at h
  obtain ⟨⟨hFM, hbits, -, hwords⟩, ⟨hFC, hpairs⟩, hD2, hD3⟩ := h
  obtain ⟨hws, -⟩ := wordsB_facts hRP hs hrt hW hwords
  subst hRP
  rw [allL_eq_true] at hFC hD2 hD3 hpairs
  have hFC' : ∀ x ∈ FC, pc (kmN (pk 32 e8Certificate.roots) (x / 256)) = x % 256 := fun x hx => by
    have e := hFC x hx
    simp only [Nat.beq_eq, nat_div_eq', nat_mod_eq'] at e
    exact e
  refine ⟨hws, fun n₀ hn₀ n₁ hn₁ => ?_⟩
  obtain ⟨h0, hf0⟩ := fixB_of_mem hrt hW hn₀
  obtain ⟨h1, hf1⟩ := fixB_of_mem hrt hW hn₁
  have m0 := mem_FL hFM hbits h0 hf0
  have m1 := mem_FL hFM hbits h1 hf1
  rw [kmL_eq] at hpairs
  have hp := hpairs _
    (List.mem_map_of_mem (f := fun n => (n, kmN (pk 32 e8Certificate.roots) n)) m0)
  simp only [allL_eq_true, kmL_eq, List.mem_map] at hp
  have hp' := hp _ ⟨n₁, m1, rfl⟩
  simp only [E7Plane.letB_eq, E7Plane.orB_eq, E7Plane.andB_eq, Bool.or_eq_true, Bool.and_eq_true,
    anyL_eq_true, memL_iff, Nat.beq_eq] at hp'
  have hσ : Nat.land (kmN (pk 32 e8Certificate.roots) n₀) (kmN (pk 32 e8Certificate.roots) n₁) =
      sgm n₀ n₁ := (congrArg₂ Nat.land (kmN_eq h0) (kmN_eq h1)).trans rfl
  have hσlt : sgm n₀ n₁ < 2 ^ 240 := by
    rw [← hσ]
    exact lt_of_le_of_lt Nat.and_le_left (kmN_lt n₀)
  rw [hσ] at hp'
  rcases hp' with ⟨m, hm, hmm⟩ | hd2 | ⟨hk, hd3⟩
  · rw [wmL_eq, List.mem_map] at hm
    obtain ⟨w, hw, rfl⟩ := hm
    have hA : ((WS.map e8PlaneWordMask).any fun m => sgm n₀ n₁ &&& m == m) = true := by
      rw [List.any_eq_true]
      refine ⟨bitsL w, ?_, beq_iff_eq.2 hmm⟩
      rw [List.mem_map]
      exact ⟨w, hw, wordMask_eq w⟩
    rw [hA, Bool.true_or, Bool.true_or]
  · have e := d2_twin hrt hW (hD2 _ hd2)
    rw [e, Bool.or_true, Bool.true_or]
  · rw [fstL_eq, List.mem_map] at hd3
    obtain ⟨⟨σ', ws⟩, hx, hσ'⟩ := hd3
    simp only at hσ'
    subst hσ'
    have e := hD3 _ hx
    simp only [E7Plane.andB_eq, Bool.and_eq_true] at e
    rw [k78_twin hFC' hk, d3_twin hrt hW e.1, d3t_twin rfl hs hrt hW hσlt e.2, Bool.true_and,
      Bool.true_and, Bool.true_or, Bool.or_true]

end CFSG.KC.E8Plane

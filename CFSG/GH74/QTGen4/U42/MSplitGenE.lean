module

public import CFSG.Quasithin.H13.A5Producer
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

@[expose] def paE : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def t3 : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 1 2

theorem paE_eq : paE = pa := rfl

theorem t3_cube : t3 * t3 * t3 = 1 := by decide

theorem pa_sq : pa * pa = 1 := by decide

theorem pa_t3_pow_five : (pa * t3) ^ 5 = 1 := by decide

theorem fix_t3 : ∀ x : W5, pact pa x = x → pact t3 x = x → x = 1 := by
  decide +kernel

theorem sq_W5 (x : W5) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  simpa using h _

theorem pact_mul_apply (σ τ : Equiv.Perm (Fin 5)) (x : W5) :
    pact (σ * τ) x = pact σ (pact τ x) := by
  rw [map_mul]
  rfl

theorem pact_one_apply (x : W5) : pact 1 x = x := by
  rw [map_one]
  rfl

theorem delta_mul (v : W5) (σ τ : Equiv.Perm (Fin 5)) :
    v * pact (σ * τ) v = (v * pact σ v) * pact σ (v * pact τ v) := by
  have e1 : pact σ (v * pact τ v) = pact σ v * pact (σ * τ) v := by
    rw [map_mul (pact σ) v (pact τ v), pact_mul_apply]
  rw [e1, pact_mul_apply]
  have h := sq_W5 (pact σ v)
  simp only [mul_assoc]
  rw [← mul_assoc (pact σ v) (pact σ v), h, one_mul]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem H1_t3 : ∀ x y : W5,
    x * pact pa x = 1 →
    y * pact t3 y * pact (t3 * t3) y = 1 →
    (x * pact pa y) * pact (pa * t3) (x * pact pa y) *
      pact ((pa * t3) * (pa * t3)) (x * pact pa y) *
      pact ((pa * t3) * (pa * t3) * (pa * t3)) (x * pact pa y) *
      pact ((pa * t3) * (pa * t3) * (pa * t3) * (pa * t3)) (x * pact pa y) = 1 →
    ∃ v : W5, x = v * pact pa v ∧ y = v * pact t3 v := by
  decide +kernel

def genE (x y : Equiv.Perm (Fin 5)) : ℕ → Finset (Equiv.Perm (Fin 5))
  | 0 => {1}
  | n + 1 =>
    let X := genE x y n
    X ∪ X.image (· * x) ∪ X.image (· * y)

theorem genE_mem (x y : Equiv.Perm (Fin 5)) : ∀ n : ℕ, ∀ z ∈ genE x y n,
    z ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 5)))
  | 0, z, hz => by
    simp only [genE, Finset.mem_singleton] at hz
    subst hz
    exact Subgroup.one_mem _
  | n + 1, z, hz => by
    simp only [genE, Finset.mem_union, Finset.mem_image] at hz
    rcases hz with (hz | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩
    · exact genE_mem x y n z hz
    · exact Subgroup.mul_mem _ (genE_mem x y n w hw) (Subgroup.subset_closure (by simp))
    · exact Subgroup.mul_mem _ (genE_mem x y n w hw) (Subgroup.subset_closure (by simp))

theorem mem_genE_of_sign : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ ∈ genE paE t3 12 := by
  decide +kernel

theorem alt_gen_pt : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
    σ ∈ Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))) := by
  intro σ hσ
  have h := genE_mem paE t3 12 σ (mem_genE_of_sign σ hσ)
  rw [paE_eq] at h
  exact h

theorem sup_decomp_V {G : Type} [Group G] {V K : Subgroup G}
    (hN : ∀ q : G, q ∈ V ⊔ K → ∀ v ∈ V, q * v * q⁻¹ ∈ V) {q : G} (hq : q ∈ V ⊔ K) :
    ∃ a ∈ K, ∃ v ∈ V, a * v = q := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ K, ∃ v ∈ V, a * v = g}
      one_mem' := ⟨1, K.one_mem, 1, V.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a1, ha1, v1, hv1, rfl⟩ ⟨a2, ha2, v2, hv2, rfl⟩
        have hc : a2⁻¹ * v1 * a2⁻¹⁻¹ ∈ V :=
          hN a2⁻¹ (Subgroup.mem_sup_right (K.inv_mem ha2)) v1 hv1
        refine ⟨a1 * a2, K.mul_mem ha1 ha2, a2⁻¹ * v1 * a2⁻¹⁻¹ * v2,
          V.mul_mem hc hv2, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, v, hv, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, a * v⁻¹ * a⁻¹, hN a (Subgroup.mem_sup_right ha) v⁻¹
          (V.inv_mem hv), by group⟩ }
  have hP : V ⊔ K ≤ P :=
    sup_le (fun v hv => ⟨1, K.one_mem, v, hv, by simp⟩)
      (fun a ha => ⟨a, ha, 1, V.one_mem, by simp⟩)
  obtain ⟨a, ha, v, hv, h⟩ : ∃ a ∈ K, ∃ v ∈ V, a * v = q := hP hq
  exact ⟨a, ha, v, hv, h⟩

theorem pa_sign_one : pa.sign = 1 := by
  rw [← paE_eq]
  show Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 3) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 5) ≠ 3 by decide)]
  rfl

theorem t3_sign_one : t3.sign = 1 := by
  show Equiv.Perm.sign (Equiv.swap (1 : Fin 5) 4 * Equiv.swap (1 : Fin 5) 2) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (1 : Fin 5) ≠ 4 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 5) ≠ 2 by decide)]
  rfl

theorem pa_t3_sign_one : (pa * t3).sign = 1 := by
  rw [Equiv.Perm.sign_mul, pa_sign_one, t3_sign_one, mul_one]

theorem cocycle_pow_five_alt (c : Equiv.Perm (Fin 5) → W5)
    (hcm : ∀ σ τ : Equiv.Perm (Fin 5), σ.sign = 1 → τ.sign = 1 →
      c (σ * τ) = c σ * pact σ (c τ))
    (w : Equiv.Perm (Fin 5)) (hw : w.sign = 1) :
    c (w ^ 5) = c w * pact w (c w) * pact (w * w) (c w) * pact (w * w * w) (c w) *
      pact (w * w * w * w) (c w) := by
  have s2 : (w * w).sign = 1 := by rw [Equiv.Perm.sign_mul, hw, mul_one]
  have s3 : (w * (w * w)).sign = 1 := by rw [Equiv.Perm.sign_mul, s2, hw, mul_one]
  have s4 : (w * (w * (w * w))).sign = 1 := by rw [Equiv.Perm.sign_mul, s3, hw, mul_one]
  rw [show w ^ 5 = w * (w * (w * (w * w))) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
    hcm w (w * (w * (w * w))) hw s4, hcm w (w * (w * w)) hw s3, hcm w (w * w) hw s2,
    hcm w w hw hw]
  simp only [map_mul, MulAut.mul_apply, mul_assoc]

theorem cocycle_coboundary_alt (c : Equiv.Perm (Fin 5) → W5) (hc1 : c 1 = 1)
    (hcm : ∀ σ τ : Equiv.Perm (Fin 5), σ.sign = 1 → τ.sign = 1 →
      c (σ * τ) = c σ * pact σ (c τ)) :
    ∃ v : W5, ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → c σ = v * pact σ v := by
  have hx : c pa * pact pa (c pa) = 1 := by
    have h := hcm pa pa pa_sign_one pa_sign_one
    rw [pa_sq, hc1] at h
    exact h.symm
  have hy : c t3 * pact t3 (c t3) * pact (t3 * t3) (c t3) = 1 := by
    have h := hcm (t3 * t3) t3 (by rw [Equiv.Perm.sign_mul, t3_sign_one, mul_one]) t3_sign_one
    rw [t3_cube, hc1, hcm t3 t3 t3_sign_one t3_sign_one] at h
    exact h.symm
  have hw : c pa * pact pa (c t3) * pact (pa * t3) (c pa * pact pa (c t3)) *
      pact (pa * t3 * (pa * t3)) (c pa * pact pa (c t3)) *
      pact (pa * t3 * (pa * t3) * (pa * t3)) (c pa * pact pa (c t3)) *
      pact (pa * t3 * (pa * t3) * (pa * t3) * (pa * t3)) (c pa * pact pa (c t3)) = 1 := by
    have h := cocycle_pow_five_alt c hcm (pa * t3) pa_t3_sign_one
    rw [pa_t3_pow_five, hc1, hcm pa t3 pa_sign_one t3_sign_one] at h
    exact h.symm
  obtain ⟨v, hv1, hv2⟩ := H1_t3 (c pa) (c t3) hx hy hw
  have hcl : ∀ σ ∈ Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))), σ.sign = 1 := by
    have hle : Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))) ≤
        Equiv.Perm.sign.ker := by
      rw [Subgroup.closure_le]
      intro x hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact MonoidHom.mem_ker.mpr pa_sign_one
      · exact MonoidHom.mem_ker.mpr t3_sign_one
    intro σ hσ
    exact MonoidHom.mem_ker.mp (hle hσ)
  have hP : ∀ σ ∈ Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))),
      c σ = v * pact σ v := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem x hx' =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact hv1
      · exact hv2
    | one => rw [hc1, pact_one_apply, sq_W5]
    | mul x y hx0 hy0 hx' hy' =>
      rw [hcm x y (hcl x hx0) (hcl y hy0), hx', hy']
      exact (delta_mul v x y).symm
    | inv x hx0 hx' =>
      have hinv : x⁻¹.sign = 1 := by rw [Equiv.Perm.sign_inv, hcl x hx0]
      have h := hcm x x⁻¹ (hcl x hx0) hinv
      rw [mul_inv_cancel, hc1] at h
      have e : pact x (c x⁻¹) = c x := by
        calc pact x (c x⁻¹) = (c x * c x) * pact x (c x⁻¹) := by rw [sq_W5, one_mul]
          _ = c x * (c x * pact x (c x⁻¹)) := by rw [mul_assoc]
          _ = c x := by rw [← h, mul_one]
      have e2 : c x⁻¹ = pact x⁻¹ (c x) := by
        rw [← e, ← pact_mul_apply, inv_mul_cancel, pact_one_apply]
      rw [e2, hx', map_mul (pact x⁻¹) v (pact x v), ← pact_mul_apply, inv_mul_cancel,
        pact_one_apply, mul_comm]
  exact ⟨v, fun σ hσ => hP σ (alt_gen_pt σ hσ)⟩

section Complement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)
include S

open Classical in
noncomputable def rgL (g : G) : Equiv.Perm (Fin 5) :=
  if hg : g ∈ L then S.frame.ρ ⟨g, S.frame.L_le hg⟩ else 1

theorem rgL_of_mem {g : G} (hg : g ∈ L) : rgL S g = S.frame.ρ ⟨g, S.frame.L_le hg⟩ := by
  unfold rgL
  simp [hg]

theorem rgL_mul {g h : G} (hg : g ∈ L) (hh : h ∈ L) :
    rgL S (g * h) = rgL S g * rgL S h := by
  rw [rgL_of_mem S hg, rgL_of_mem S hh, rgL_of_mem S (L.mul_mem hg hh), ← map_mul]
  rfl

theorem rgL_inv {g : G} (hg : g ∈ L) : rgL S g⁻¹ = (rgL S g)⁻¹ := by
  rw [rgL_of_mem S hg, rgL_of_mem S (L.inv_mem hg), ← map_inv]
  rfl

theorem rgL_V (hVL : V ≤ L) {v : G} (hv : v ∈ V) : rgL S v = 1 := by
  rw [rgL_of_mem S (hVL hv)]
  refine S.frame.rho_eq_one_of_mem _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact B2F.isElemAbelian_comm S.elemAbelian_V hw hv

theorem rgL_sign {g : G} (hg : g ∈ L) : (rgL S g).sign = 1 :=
  (S.frame.image_L (rgL S g)).1 ⟨⟨g, S.frame.L_le hg⟩, hg, (rgL_of_mem S hg).symm⟩

theorem mem_V_of_rgL_eq_one (hO : pCoreOf 2 (L ⊔ T) = V) {g : G} (hg : g ∈ L)
    (h1 : rgL S g = 1) : g ∈ V := by
  rw [rgL_of_mem S hg] at h1
  have hc : g ∈ Subgroup.centralizer (V : Set G) :=
    S.frame.mem_centralizer_of_rho ⟨g, S.frame.L_le hg⟩ h1
  have hmem : g ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := ⟨Subgroup.mem_sup_left hg, hc⟩
  rw [S.cLT, hO] at hmem
  exact hmem

theorem eq_of_rgL_eq (hO : pCoreOf 2 (L ⊔ T) = V) {K : Subgroup G}
    (hK : K ≤ L) (hKV : K ⊓ V = ⊥) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (h : rgL S x = rgL S y) : x = y := by
  have hxL : x ∈ L := hK hx
  have hyL : y ∈ L := hK hy
  have h1 : rgL S (x * y⁻¹) = 1 := by
    rw [rgL_mul S hxL (L.inv_mem hyL), rgL_inv S hyL, h, mul_inv_cancel]
  have hzV : x * y⁻¹ ∈ V := mem_V_of_rgL_eq_one S hO (L.mul_mem hxL (L.inv_mem hyL)) h1
  have hz : x * y⁻¹ ∈ K ⊓ V := ⟨K.mul_mem hx (K.inv_mem hy), hzV⟩
  rw [hKV] at hz
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hz)

theorem rgL_one : rgL S 1 = 1 := by
  rw [rgL_of_mem S L.one_mem]
  exact map_one _

theorem exists_rgL_eq {K : Subgroup G} (hVL : V ≤ L) (hK : K ≤ L) (hKL : V ⊔ K = L)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) : ∃ a ∈ K, rgL S a = σ := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
  have hq : (g : G) ∈ V ⊔ K := by rw [hKL]; exact hgL
  have hN : ∀ q : G, q ∈ V ⊔ K → ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq' v hv
    have hqL : q ∈ L := by rw [← hKL]; exact hq'
    exact (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hqL) v).mp hv
  obtain ⟨a, ha, v, hv, hav⟩ := sup_decomp_V hN hq
  have hsplit : rgL S (g : G) = rgL S a * rgL S v := by
    rw [← hav, rgL_mul S (hK ha) (hVL hv)]
  rw [rgL_V S hVL hv, mul_one, rgL_of_mem S hgL] at hsplit
  exact ⟨a, ha, by rw [← hsplit]; exact hg⟩

open Classical in
noncomputable def pickE (K : Subgroup G) (σ : Equiv.Perm (Fin 5)) : G :=
  Classical.epsilon (fun a : G => a ∈ K ∧ rgL S a = σ)

theorem pickE_spec {K : Subgroup G} (hVL : V ≤ L) (hK : K ≤ L) (hKL : V ⊔ K = L)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) :
    pickE S K σ ∈ K ∧ rgL S (pickE S K σ) = σ := by
  obtain ⟨a, ha, h⟩ := exists_rgL_eq S hVL hK hKL hσ
  exact Classical.epsilon_spec (p := fun b : G => b ∈ K ∧ rgL S b = σ) ⟨a, ha, h⟩

theorem u_mem (hO : pCoreOf 2 (L ⊔ T) = V) (hVL : V ≤ L) {A B : Subgroup G}
    (hA : A ≤ L) (hAL : V ⊔ A = L) (hB : B ≤ L) (hBL : V ⊔ B = L)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) :
    pickE S B σ * (pickE S A σ)⁻¹ ∈ V := by
  obtain ⟨hbB, hbρ⟩ := pickE_spec S hVL hB hBL hσ
  obtain ⟨haA, haρ⟩ := pickE_spec S hVL hA hAL hσ
  apply mem_V_of_rgL_eq_one S hO (L.mul_mem (hB hbB) (L.inv_mem (hA haA)))
  rw [rgL_mul S (hB hbB) (L.inv_mem (hA haA)), rgL_inv S (hA haA), hbρ, haρ, mul_inv_cancel]

open Classical in
noncomputable def cocE {A B : Subgroup G} (hO : pCoreOf 2 (L ⊔ T) = V) (hVL : V ≤ L)
    (hA : A ≤ L) (hAL : V ⊔ A = L) (hB : B ≤ L) (hBL : V ⊔ B = L)
    (σ : Equiv.Perm (Fin 5)) : W5 :=
  if h : σ.sign = 1 then
    S.frame.ψ ⟨pickE S B σ * (pickE S A σ)⁻¹, u_mem S hO hVL hA hAL hB hBL h⟩
  else 1

theorem cocE_eq {A B : Subgroup G} (hO : pCoreOf 2 (L ⊔ T) = V) (hVL : V ≤ L)
    (hA : A ≤ L) (hAL : V ⊔ A = L) (hB : B ≤ L) (hBL : V ⊔ B = L)
    {σ : Equiv.Perm (Fin 5)} (h : σ.sign = 1) :
    cocE S hO hVL hA hAL hB hBL σ =
      S.frame.ψ ⟨pickE S B σ * (pickE S A σ)⁻¹, u_mem S hO hVL hA hAL hB hBL h⟩ := by
  simp [cocE, h]

theorem conj_mem_V {h v : G} (hh : h ∈ L) (hv : v ∈ V) : h * v * h⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hh) v).mp hv

theorem pickE_mul {A : Subgroup G} (hO : pCoreOf 2 (L ⊔ T) = V) (hVL : V ≤ L) (hA : A ≤ L)
    (hAL : V ⊔ A = L) (hAV : A ⊓ V = ⊥) {σ τ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1)
    (hτ : τ.sign = 1) : pickE S A (σ * τ) = pickE S A σ * pickE S A τ := by
  have hστ : (σ * τ).sign = 1 := by rw [Equiv.Perm.sign_mul, hσ, hτ, mul_one]
  have h1 := pickE_spec S hVL hA hAL hσ
  have h2 := pickE_spec S hVL hA hAL hτ
  have h3 := pickE_spec S hVL hA hAL hστ
  exact eq_of_rgL_eq S hO hA hAV h3.1 (A.mul_mem h1.1 h2.1)
    (by rw [h3.2, rgL_mul S (hA h1.1) (hA h2.1), h1.2, h2.2])

theorem cocE_mul {A B : Subgroup G} (hO : pCoreOf 2 (L ⊔ T) = V) (hVL : V ≤ L)
    (hA : A ≤ L) (hAL : V ⊔ A = L) (hAV : A ⊓ V = ⊥)
    (hB : B ≤ L) (hBL : V ⊔ B = L) (hBV : B ⊓ V = ⊥)
    {σ τ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) (hτ : τ.sign = 1) :
    cocE S hO hVL hA hAL hB hBL (σ * τ) =
      cocE S hO hVL hA hAL hB hBL σ * pact σ (cocE S hO hVL hA hAL hB hBL τ) := by
  have hστ : (σ * τ).sign = 1 := by rw [Equiv.Perm.sign_mul, hσ, hτ, mul_one]
  have haσ : pickE S A σ ∈ A := (pickE_spec S hVL hA hAL hσ).1
  have hρσ : S.frame.ρ ⟨pickE S A σ, S.frame.L_le (hA haσ)⟩ = σ := by
    rw [← rgL_of_mem S (hA haσ)]
    exact (pickE_spec S hVL hA hAL hσ).2
  have huστ := u_mem S hO hVL hA hAL hB hBL hστ
  have huσ := u_mem S hO hVL hA hAL hB hBL hσ
  have huτ := u_mem S hO hVL hA hAL hB hBL hτ
  have hconjmem : pickE S A σ * (pickE S B τ * (pickE S A τ)⁻¹) * (pickE S A σ)⁻¹ ∈ V :=
    conj_mem_V S (hA haσ) huτ
  have hconjτ : S.frame.ψ ⟨pickE S A σ * (pickE S B τ * (pickE S A τ)⁻¹) * (pickE S A σ)⁻¹,
      hconjmem⟩ = pact σ (cocE S hO hVL hA hAL hB hBL τ) := by
    rw [cocE_eq S hO hVL hA hAL hB hBL hτ]
    have h := S.psi_conj ⟨pickE S A σ, S.frame.L_le (hA haσ)⟩
      ⟨pickE S B τ * (pickE S A τ)⁻¹, huτ⟩
    rw [hρσ] at h
    exact h
  have hbστ : pickE S B (σ * τ) = pickE S B σ * pickE S B τ :=
    pickE_mul S hO hVL hB hBL hBV hσ hτ
  have haστ : pickE S A (σ * τ) = pickE S A σ * pickE S A τ :=
    pickE_mul S hO hVL hA hAL hAV hσ hτ
  have hX : (⟨_, huστ⟩ : ↥V) = ⟨_, huσ⟩ * ⟨_, hconjmem⟩ := Subtype.ext (by
    show pickE S B (σ * τ) * (pickE S A (σ * τ))⁻¹ =
      (pickE S B σ * (pickE S A σ)⁻¹) *
        (pickE S A σ * (pickE S B τ * (pickE S A τ)⁻¹) * (pickE S A σ)⁻¹)
    rw [hbστ, haστ]
    group)
  calc cocE S hO hVL hA hAL hB hBL (σ * τ)
      = S.frame.ψ ⟨_, huστ⟩ := cocE_eq S hO hVL hA hAL hB hBL hστ
    _ = S.frame.ψ (⟨_, huσ⟩ * ⟨_, hconjmem⟩) := congrArg S.frame.ψ hX
    _ = S.frame.ψ ⟨_, huσ⟩ * S.frame.ψ ⟨_, hconjmem⟩ := map_mul _ _ _
    _ = cocE S hO hVL hA hAL hB hBL σ * pact σ (cocE S hO hVL hA hAL hB hBL τ) := by
        rw [hconjτ, cocE_eq S hO hVL hA hAL hB hBL hσ]

theorem complement_conj (hO : pCoreOf 2 (L ⊔ T) = V) {A B : Subgroup G}
    (hA : A ≤ L) (hAV : A ⊓ V = ⊥) (hAL : V ⊔ A = L)
    (hB : B ≤ L) (hBV : B ⊓ V = ⊥) (hBL : V ⊔ B = L) :
    ∃ w ∈ V, ∀ x : G, x ∈ B ↔ w⁻¹ * x * w ∈ A := by
  have hVL : V ≤ L := by rw [← hAL]; exact le_sup_left
  have one_sign : (1 : Equiv.Perm (Fin 5)).sign = 1 := by simp
  have hpB1 : pickE S B 1 = 1 :=
    eq_of_rgL_eq S hO hB hBV (pickE_spec S hVL hB hBL one_sign).1 B.one_mem
      (by rw [(pickE_spec S hVL hB hBL one_sign).2, rgL_one])
  have hpA1 : pickE S A 1 = 1 :=
    eq_of_rgL_eq S hO hA hAV (pickE_spec S hVL hA hAL one_sign).1 A.one_mem
      (by rw [(pickE_spec S hVL hA hAL one_sign).2, rgL_one])
  have hcone1 : cocE S hO hVL hA hAL hB hBL 1 = 1 := by
    have e : (⟨pickE S B 1 * (pickE S A 1)⁻¹, u_mem S hO hVL hA hAL hB hBL one_sign⟩ : ↥V) = 1 :=
      Subtype.ext (by
        show pickE S B 1 * (pickE S A 1)⁻¹ = 1
        rw [hpB1, hpA1, inv_one, mul_one])
    rw [cocE_eq S hO hVL hA hAL hB hBL one_sign, e, map_one]
  obtain ⟨v, hv⟩ := cocycle_coboundary_alt (cocE S hO hVL hA hAL hB hBL) hcone1
    (fun σ τ hσ hτ => cocE_mul S hO hVL hA hAL hAV hB hBL hBV hσ hτ)
  obtain ⟨W, hW⟩ : ∃ W : ↥V, S.frame.ψ W = v :=
    ⟨S.frame.ψ.symm v, MulEquiv.apply_symm_apply _ v⟩
  have hWW : W * W = 1 := S.frame.ψ.injective (by rw [map_mul, map_one, hW, sq_W5])
  have hw2 : (W : G) * (W : G) = 1 := congrArg Subtype.val hWW
  have hwinv : (W : G)⁻¹ = (W : G) := inv_eq_of_mul_eq_one_right hw2
  have key : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
      pickE S B σ = (W : G)⁻¹ * pickE S A σ * (W : G) := by
    intro σ hσ
    have haA : pickE S A σ ∈ A := (pickE_spec S hVL hA hAL hσ).1
    have hρ : S.frame.ρ ⟨pickE S A σ, S.frame.L_le (hA haA)⟩ = σ := by
      rw [← rgL_of_mem S (hA haA)]
      exact (pickE_spec S hVL hA hAL hσ).2
    have hYmem : pickE S A σ * (W : G) * (pickE S A σ)⁻¹ ∈ V :=
      conj_mem_V S (hA haA) W.2
    have hY : S.frame.ψ ⟨pickE S A σ * (W : G) * (pickE S A σ)⁻¹, hYmem⟩ = pact σ v := by
      have h := S.psi_conj ⟨pickE S A σ, S.frame.L_le (hA haA)⟩ W
      rw [hρ, hW] at h
      exact h
    have huσ := u_mem S hO hVL hA hAL hB hBL hσ
    have hcσ : S.frame.ψ ⟨pickE S B σ * (pickE S A σ)⁻¹, huσ⟩ = v * pact σ v := by
      rw [← cocE_eq S hO hVL hA hAL hB hBL hσ]
      exact hv σ hσ
    have hmain : W * ⟨pickE S A σ * (W : G) * (pickE S A σ)⁻¹, hYmem⟩ =
        ⟨pickE S B σ * (pickE S A σ)⁻¹, huσ⟩ :=
      S.frame.ψ.injective (by rw [map_mul, hW, hY, hcσ])
    have hG : (W : G) * (pickE S A σ * (W : G) * (pickE S A σ)⁻¹) =
        pickE S B σ * (pickE S A σ)⁻¹ := congrArg Subtype.val hmain
    calc pickE S B σ = pickE S B σ * (pickE S A σ)⁻¹ * pickE S A σ := by group
      _ = (W : G) * (pickE S A σ * (W : G) * (pickE S A σ)⁻¹) * pickE S A σ := by rw [hG]
      _ = (W : G)⁻¹ * pickE S A σ * (W : G) := by rw [hwinv]; group
  refine ⟨(W : G), W.2, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  ·
    have hxL : x ∈ L := hB hx
    have hσ : (rgL S x).sign = 1 := rgL_sign S hxL
    have hxeq : x = pickE S B (rgL S x) :=
      eq_of_rgL_eq S hO hB hBV hx (pickE_spec S hVL hB hBL hσ).1
        (by rw [(pickE_spec S hVL hB hBL hσ).2])
    rw [hxeq, key _ hσ]
    have e : (W : G)⁻¹ * ((W : G)⁻¹ * pickE S A (rgL S x) * (W : G)) * (W : G) =
        pickE S A (rgL S x) := by
      rw [hwinv]
      calc (W : G) * ((W : G) * pickE S A (rgL S x) * (W : G)) * (W : G)
          = ((W : G) * (W : G)) * pickE S A (rgL S x) * ((W : G) * (W : G)) := by group
        _ = pickE S A (rgL S x) := by rw [hw2, one_mul, mul_one]
    rw [e]
    exact (pickE_spec S hVL hA hAL hσ).1
  ·
    obtain ⟨σ, hσdef⟩ : ∃ σ : Equiv.Perm (Fin 5), rgL S ((W : G)⁻¹ * x * (W : G)) = σ :=
      ⟨_, rfl⟩
    have hyL : (W : G)⁻¹ * x * (W : G) ∈ L := hA hx
    have hσ : σ.sign = 1 := by rw [← hσdef]; exact rgL_sign S hyL
    have hpA : pickE S A σ ∈ A := (pickE_spec S hVL hA hAL hσ).1
    have hyeq : (W : G)⁻¹ * x * (W : G) = pickE S A σ :=
      eq_of_rgL_eq S hO hA hAV hx hpA
        (by rw [(pickE_spec S hVL hA hAL hσ).2, hσdef])
    have hxa : x = (W : G) * pickE S A σ * (W : G) := by
      calc x = (W : G) * ((W : G)⁻¹ * x * (W : G)) * (W : G)⁻¹ := by group
        _ = (W : G) * pickE S A σ * (W : G)⁻¹ := by rw [hyeq]
        _ = (W : G) * pickE S A σ * (W : G) := by rw [hwinv]
    have hxB : x = pickE S B σ := by
      rw [key σ hσ, hxa, hwinv]
    rw [hxB]
    exact (pickE_spec S hVL hB hBL hσ).1

end Complement

end CFSG.GH74.QTGen4.U42

end

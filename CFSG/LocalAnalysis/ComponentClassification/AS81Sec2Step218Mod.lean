module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Mat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Odd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2LocalQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step215

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2V4
open scoped commutatorElement

namespace Sec2

variable {G : Type} [Group G] [Finite G]

theorem exists_two_mul_odd_of (k : G) :
    ∃ y ∈ zpowers k, (∃ n : ℕ, y ^ 2 ^ n = 1) ∧ ∃ w ∈ zpowers k, Odd (orderOf w) ∧ k = y * w := by
  have hn : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ e) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set a := Nat.gcdA (2 ^ e) m
  set b := Nat.gcdB (2 ^ e) m
  refine ⟨k ^ ((m : ℤ) * b), zpow_mem (mem_zpowers k) _, ⟨e, ?_⟩, k ^ ((2 : ℤ) ^ e * a),
    zpow_mem (mem_zpowers k) _, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * b * ((2 ^ e : ℕ) : ℤ) =
      ((2 ^ e * m : ℕ) : ℤ) * b by push_cast; ring, ← hnm, zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, one_zpow]
  · have hdvd : orderOf (k ^ ((2 : ℤ) ^ e * a)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, show (2 : ℤ) ^ e * a * (m : ℤ) =
        ((2 ^ e * m : ℕ) : ℤ) * a by push_cast; ring, ← hnm, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow]
    exact hm.of_dvd_nat hdvd
  · rw [← zpow_add, show (m : ℤ) * b + 2 ^ e * a = 1 by rw [hbez]; push_cast; ring, zpow_one]

section Special

variable {S Z : Subgroup G}

omit [Finite G] in
theorem mul_conj_eq_of_odd (hS : Special S Z) {e : G} (heZ : ∀ c ∈ Z, e * c * e⁻¹ = c)
    (heSZ : ∀ s ∈ S, e * s * e⁻¹ * s⁻¹ ∈ Z) {m : ℕ} (hm : Odd m) (hem : e ^ m = 1) {s : G}
    (hs : s ∈ S) : e * s * e⁻¹ = s := by
  set ζ := e * s * e⁻¹ * s⁻¹ with hζ
  have hζZ : ζ ∈ Z := heSZ s hs
  have hes : e * s * e⁻¹ = ζ * s := by rw [hζ]; group
  have hpow : ∀ k : ℕ, e ^ k * s * (e ^ k)⁻¹ = ζ ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : e * ζ ^ k * e⁻¹ = ζ ^ k := by
        rw [← conj_pow, heZ ζ hζZ]
      calc e ^ (k + 1) * s * (e ^ (k + 1))⁻¹ = e * (e ^ k * s * (e ^ k)⁻¹) * e⁻¹ := by group
        _ = e * (ζ ^ k * s) * e⁻¹ := by rw [ih]
        _ = (e * ζ ^ k * e⁻¹) * (e * s * e⁻¹) := by group
        _ = ζ ^ k * (ζ * s) := by rw [h1, hes]
        _ = ζ ^ (k + 1) * s := by rw [pow_succ]; group
  have h1 := hpow m
  rw [hem, one_mul, inv_one, mul_one] at h1
  have hζm : ζ ^ m = 1 := by
    have := congrArg (· * s⁻¹) h1
    simpa using this.symm
  obtain ⟨j, rfl⟩ := hm
  have hζ2 : ζ ^ 2 = 1 := by rw [sq]; exact hS.elem ζ hζZ
  have hζ1 : ζ = 1 := by
    rw [pow_succ, pow_mul, hζ2, one_pow, one_mul] at hζm
    exact hζm
  rw [hes, hζ1, one_mul]

omit [Finite G] in
theorem comm_mul_Z_mul_Z (hS : Special S Z) {a b c₁ c₂ : G} (ha : a ∈ S) (hb : b ∈ S)
    (hc₁ : c₁ ∈ Z) (hc₂ : c₂ ∈ Z) :
    (c₁ * a) * (c₂ * b) * (c₁ * a)⁻¹ * (c₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  rw [hS.comm_Z hc₁ ha, hS.comm_Z hc₂ hb]
  have hac : a * c₁ ∈ S := S.mul_mem ha (hS.le hc₁)
  rw [hS.comm_mul_Z hac hb hc₂]
  calc a * c₁ * b * (a * c₁)⁻¹ * b⁻¹ = (b * (a * c₁) * b⁻¹ * (a * c₁)⁻¹)⁻¹ := by group
    _ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by rw [hS.comm_mul_Z hb ha hc₁]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem conj_eq_of_conj_mem (hS : Special S Z) {g g' : G} (hg' : g' ∈ normalizer (S : Set G))
    (h : ∀ s ∈ S, (g * s * g⁻¹) * (g' * s * g'⁻¹)⁻¹ ∈ Z) {c : G} (hc : c ∈ Z) :
    g * c * g⁻¹ = g' * c * g'⁻¹ := by
  have hgs' : ∀ {a : G}, a ∈ S → g' * a * g'⁻¹ ∈ S := fun ha =>
    (mem_normalizer_iff.mp hg' _).mp ha
  have hle : ⁅S, S⁆ ≤ centralizer ({g'⁻¹ * g} : Set G) := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_centralizer_singleton_iff]
    have hz1 := h a ha
    have hz2 := h b hb
    have ha' : g * a * g⁻¹ = ((g * a * g⁻¹) * (g' * a * g'⁻¹)⁻¹) * (g' * a * g'⁻¹) := by group
    have hb' : g * b * g⁻¹ = ((g * b * g⁻¹) * (g' * b * g'⁻¹)⁻¹) * (g' * b * g'⁻¹) := by group
    have key : g * ⁅a, b⁆ * g⁻¹ = g' * ⁅a, b⁆ * g'⁻¹ := by
      have e1 : g * ⁅a, b⁆ * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ *
          (g * b * g⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      have e2 : g' * ⁅a, b⁆ * g'⁻¹ = (g' * a * g'⁻¹) * (g' * b * g'⁻¹) * (g' * a * g'⁻¹)⁻¹ *
          (g' * b * g'⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1, e2, ha', hb', comm_mul_Z_mul_Z hS (hgs' ha) (hgs' hb) hz1 hz2]
    calc ⁅a, b⁆ * (g'⁻¹ * g) = g'⁻¹ * (g' * ⁅a, b⁆ * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * ⁅a, b⁆ * g⁻¹) * g := by rw [key]
      _ = g'⁻¹ * g * ⁅a, b⁆ := by group
  have hc' : c ∈ centralizer ({g'⁻¹ * g} : Set G) := hle (by rw [hS.comm]; exact hc)
  rw [mem_centralizer_singleton_iff] at hc'
  calc g * c * g⁻¹ = g' * (g'⁻¹ * g * c) * g⁻¹ := by group
    _ = g' * (c * (g'⁻¹ * g)) * g⁻¹ := by rw [hc']
    _ = g' * c * g'⁻¹ := by group

end Special

section Mats

variable {S Z H : Subgroup G}

omit [Finite G] in
theorem Coord.mat_mul (C : Coord S Z H) {g g' : G} {M M' : Mat2}
    (hg' : g' ∈ normalizer (S : Set G)) (hM : ∀ s ∈ S, C.Ψ (g * s * g⁻¹) = matAct M (C.Ψ s))
    (hM' : ∀ s ∈ S, C.Ψ (g' * s * g'⁻¹) = matAct M' (C.Ψ s)) :
    ∀ s ∈ S, C.Ψ ((g * g') * s * (g * g')⁻¹) = matAct (matMul M M') (C.Ψ s) := by
  intro s hs
  have e : (g * g') * s * (g * g')⁻¹ = g * (g' * s * g'⁻¹) * g⁻¹ := by group
  rw [e, hM _ ((mem_normalizer_iff.mp hg' s).mp hs), hM' s hs, matAct_matMul]

omit [Finite G] in
theorem Coord.mat_unique (C : Coord S Z H) {g : G} {M M' : Mat2}
    (hM : ∀ s ∈ S, C.Ψ (g * s * g⁻¹) = matAct M (C.Ψ s))
    (hM' : ∀ s ∈ S, C.Ψ (g * s * g⁻¹) = matAct M' (C.Ψ s)) : M = M' := by
  refine mat_eq_of_matAct fun m hm1 hm2 => ?_
  obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
  rw [Prod.mk.eta] at hsm
  rw [← hsm, ← hM s hs, hM' s hs]

omit [Finite G] in
theorem Coord.mat_one (C : Coord S Z H) :
    ∀ s ∈ S, C.Ψ ((1 : G) * s * 1⁻¹) = matAct matOne (C.Ψ s) := by
  intro s _
  rw [matAct_matOne]
  simp

omit [Finite G] in
theorem Coord.mul_inv_mem_of_mat_one (C : Coord S Z H) (hS : Special S Z) {g : G}
    (hg : g ∈ normalizer (S : Set G)) (hM : ∀ s ∈ S, C.Ψ (g * s * g⁻¹) = matAct matOne (C.Ψ s)) :
    ∀ s ∈ S, (g * s * g⁻¹) * s⁻¹ ∈ Z := by
  intro s hs
  rw [← C.Ψ_eq_iff hS ((mem_normalizer_iff.mp hg s).mp hs) hs, hM s hs, matAct_matOne]

omit [Finite G] in
theorem Special.normalizer_le (hS : Special S Z) :
    normalizer (S : Set G) ≤ normalizer (Z : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact fun hc => conj_mem_Z_of_normS hS hn hc
  · intro hc
    have h := conj_mem_Z_of_normS hS (inv_mem hn) hc
    simpa [mul_assoc] using h

omit [Finite G] in
theorem mem_centralizerMod_of (hS : Special S Z) {g : G} (hg : g ∈ normalizer (S : Set G))
    (hgZ : ∀ s ∈ S, (g * s * g⁻¹) * s⁻¹ ∈ Z) :
    g ∈ centralizerMod (normalizer (S : Set G)) S Z := by
  refine ⟨hg, hS.normalizer_le hg, fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (mem_normalizer_iff.mp (inv_mem hg) s).mp hs
    simpa using this
  have h1 := hgZ _ hs'
  have e1 : g * (g⁻¹ * s * g) * g⁻¹ * (g⁻¹ * s * g)⁻¹ = s * g⁻¹ * s⁻¹ * g := by group
  rw [e1] at h1
  have e2 : s⁻¹ * g⁻¹ * s * g = s⁻¹ * (s * g⁻¹ * s⁻¹ * g)⁻¹ * s := by group
  rw [e2, hS.conj_Z' (Z.inv_mem h1) hs]
  exact Z.inv_mem h1

theorem mem_of_mem_centralizerMod
    (hsyl : IsSylowOf 2 S (centralizerMod (normalizer (S : Set G)) S Z)) {g : G}
    (hg : g ∈ centralizerMod (normalizer (S : Set G)) S Z) {n : ℕ} (hn : g ^ 2 ^ n = 1) :
    g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (zpowers g) := IsPGroup.of_card (n := (Nat.card (zpowers g)).factorization 2)
    (by
      have hdvd : Nat.card (zpowers g) ∣ 2 ^ n := by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hn
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hj, Nat.prime_two.factorization_pow, Finsupp.single_eq_same])
  have hP := IsPGroup.to_sup_of_normal_left' hsyl.isPGroup hgp (zpowers_le.mpr hg.1)
  have heq := hsyl.eq_of_le le_sup_left (sup_le hsyl.le (zpowers_le.mpr hg)) hP
  exact heq ▸ (mem_sup_right (mem_zpowers g))

end Mats

theorem matAct_add3 (A B C' : Mat2) (m : Pair) :
    matAct (fun i j => A i j + B i j + C' i j) m = matAct A m + matAct B m + matAct C' m := by
  simp only [matAct, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;>
  · funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem matAct_zero (m : Pair) : matAct 0 m = 0 := by
  simp [matAct]

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

open Sec2

theorem exists_qsetting (h21 : Step21) (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) {x : G} (hx3 : orderOf x = 3)
    (hxF4 : ActsAsF4Scalar x (sec2S A R E F) (sec2Z A E F))
    (hxcl : closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * x⁻¹ * w * x} = sec2Z A E F)
    (hxH : x ∈ normalizer (sec2H E F : Set G))
    (hxH' : ∀ h ∈ sec2H E F, x⁻¹ * h⁻¹ * x * h ∈ sec2S A R E F)
    (hθx : ∃ θ : ↥(sec2H E F ⊔ zpowers x ⊔ sec2T E T₀) →*
        Equiv.Perm (Fin 3) × alternatingGroup (Fin 5),
      Function.Surjective θ ∧ θ.ker = (sec2S A R E F).subgroupOf (sec2H E F ⊔ zpowers x ⊔ sec2T E T₀)) :
    ∃ (_ : Coord (sec2S A R E F) (sec2Z A E F) (sec2H E F)) (t z₁ : G)
      (hD : QSetting (sec2S A R E F) (sec2Z A E F) (sec2H E F) x t z₁),
      hD.Q = Q ∧ t ∈ sec2T E T₀ ∧ ∀ τ ∈ sec2T E T₀, τ ∈ sec2H E F ∨ t * τ ∈ sec2H E F := by
  have hd := hQ.data
  have hset := hd.setting
  have hS : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hset
  obtain ⟨C⟩ := nonempty_coord h26 hset
  obtain ⟨-, hSH, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hset
  obtain ⟨-, hPE, -, -, -, -, -, -, hSPE, -⟩ := h21 G A R g E F hset
  obtain ⟨-, hPST, -, -, -, -⟩ := (h212 G A R g E F hset).2 T₀ hd.le hd.sylow
  obtain ⟨θ, hθ, hker⟩ := hθx
  have hx : XData (sec2S A R E F) (sec2Z A E F) x :=
    ⟨hxF4.1, hxF4.2.1, by rw [← hx3, pow_orderOf_eq_one], hxcl, hxF4.2.2⟩
  have hT₀2 : IsPGroup 2 T₀ := hd.sylow.isPGroup
  have hT2 : IsPGroup 2 (sec2T E T₀) := hT₀2.to_le inf_le_left
  have hST : sec2S A R E F ≤ sec2T E T₀ := le_sup_right.trans hPST
  have hS2 : IsPGroup 2 (sec2S A R E F) := hT2.to_le hST
  have hKN : sec2H E F ⊔ sec2T E T₀ ⊔ zpowers x ≤ normalizer (sec2S A R E F : Set G) :=
    sup_le (sup_le hHS (inf_le_left.trans hd.sylow.le)) (zpowers_le.mpr hxF4.1)
  obtain ⟨hinf, hsup⟩ := semidirect C hS hx hker hS2 hx3 hxH'
    (hSH.trans (le_sup_left.trans le_sup_left))
  have hPH : sec2P E ≤ sec2H E F := le_sup_left
  have hP4 : (sec2S A R E F).relIndex (sec2P E) = 4 := by
    have h1 := Subgroup.relIndex_mul_relIndex E (sec2S A R E F ⊓ sec2P E) (sec2P E) hSPE.1
      inf_le_right
    rw [hSPE.2.1, hPE.2.1, Subgroup.inf_relIndex_right] at h1
    omega
  have hP4' : (sec2P E ⊓ sec2S A R E F).relIndex (sec2P E) = 4 := by
    rw [Subgroup.inf_relIndex_left]
    exact hP4
  obtain ⟨t₀, ht₀, h0, h1, h2⟩ := exists_t₀ C hθ hker hS2 hT2 hx3 hxH'
    (le_sup_left.trans hPST) hPH hP4'
  obtain ⟨t, htT, htt, htx, htS, htN, hcompl, hTH, -, -⟩ := exists_t C hker hSH hST hS2 hT2 hx3
    (θ_x C hker hS2 hx3 hxH') hKN hinf hsup ht₀ h0 h1 h2
  have ht : TData (sec2S A R E F) (sec2H E F) x t := ⟨htN, htt, htx, htS, hcompl⟩
  obtain ⟨z', hzZ, hz1, hz⟩ := exists_z hS hx ht
  have hD : QSetting (sec2S A R E F) (sec2Z A E F) (sec2H E F) x t z' :=
    ⟨hS, hSH, hHS, hx, hxH, hxH', ht, hzZ, hz1, hz⟩
  have hyH : y ∈ sec2H E F := hd.uy.2.2.2.1.1.1
  have hQHT : sec2H E F ⊔ sec2T E T₀ ≤ normalizer (hD.Q : Set G) :=
    C.le_normalizer_Qt hS hHS ht hTH
  have hQeq : hD.Q = Q := hQ.unique _ (C.isQ8Cube_Qt hS hHS hx ht hzZ hz1 hz) (hD.Q_le hST htT)
    (hQHT (mem_sup_left hyH))
  exact ⟨C, t, z', hD, hQeq, htT, hTH⟩

theorem mem_normalizer_of_mem_normalizer_sec2S
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21)
    (h24 : Step24) (h26 : Step26) (h211 : Step211) (h212 : Step212)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) {x : G} (hx3 : orderOf x = 3)
    (hxF4 : ActsAsF4Scalar x (sec2S A R E F) (sec2Z A E F))
    (hxcl : closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * x⁻¹ * w * x} = sec2Z A E F)
    (hxH : x ∈ normalizer (sec2H E F : Set G))
    (hxH' : ∀ h ∈ sec2H E F, x⁻¹ * h⁻¹ * x * h ∈ sec2S A R E F)
    (hθx : ∃ θ : ↥(sec2H E F ⊔ zpowers x ⊔ sec2T E T₀) →*
        Equiv.Perm (Fin 3) × alternatingGroup (Fin 5),
      Function.Surjective θ ∧ θ.ker = (sec2S A R E F).subgroupOf (sec2H E F ⊔ zpowers x ⊔ sec2T E T₀))
    {w : G} (hwS : w ∈ normalizer (sec2S A R E F : Set G)) (hwz : w ∈ centralizer ({z} : Set G)) :
    w ∈ normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, t, z₁, hD, hQeq, htT, hTH⟩ :=
    exists_qsetting h21 h24 h26 h212 hQ hx3 hxF4 hxcl hxH hxH' hθx
  have hd := hQ.data
  have hset := hd.setting
  have hSp := hD.hS
  obtain ⟨-, hSH, -, -, -, hsylS, -, hHS, hNH⟩ := h26 G A R g E F hset
  have ht := hD.ht
  have hx := hD.hx
  have hT₀2 : IsPGroup 2 T₀ := hd.sylow.isPGroup
  obtain ⟨-, hPST, -⟩ := (h212 G A R g E F hset).2 T₀ hd.le hd.sylow
  have hST : sec2S A R E F ≤ sec2T E T₀ := le_sup_right.trans hPST
  have htQ : t ∈ Q := hQeq ▸ hSp.t_mem_Qt ht.normS ht.sq
  have hzZ : z ∈ sec2Z A E F := z_mem_Z h212 hQ
  have hz1 : z ≠ 1 := by
    intro h
    have := hQ.order
    rw [h, orderOf_one] at this
    omega
  have htz : t * z * t⁻¹ = z := by
    have h1 : t * z = z * t := mem_centralizer_iff.mp hQ.z_mem_centralizer_Q t htQ
    rw [h1, mul_inv_cancel_right]
  have hwz' : w * z * w⁻¹ = z := by
    have h1 : z * w = w * z := mem_centralizer_iff.mp hwz z rfl
    rw [← h1, mul_inv_cancel_right]
  have hwH : w ∈ normalizer (sec2H E F : Set G) := hNH hwS
  have htH : ∀ h ∈ sec2H E F, t * h * t⁻¹ * h⁻¹ ∈ sec2S A R E F := by
    intro h hh
    obtain ⟨s, hs, l, hl, rfl, hlt⟩ := ht.compl h hh
    have e : t * (s * l) * t⁻¹ * (s * l)⁻¹ = (t * s * t⁻¹) * (t * l * t⁻¹ * l⁻¹) * s⁻¹ := by
      group
    have hl' : t * l * t⁻¹ * l⁻¹ = 1 := by rw [← hlt]; group
    rw [e, hl', mul_one]
    exact (sec2S A R E F).mul_mem ((mem_normalizer_iff.mp ht.normS s).mp hs)
      ((sec2S A R E F).inv_mem hs)
  set d := w * t * w⁻¹ with hddef
  have hdS : d ∈ normalizer (sec2S A R E F : Set G) := mul_mem (mul_mem hwS ht.normS) (inv_mem hwS)
  have hdH : ∀ h ∈ sec2H E F, d * h * d⁻¹ * h⁻¹ ∈ sec2S A R E F := by
    intro h hh
    have hh' : w⁻¹ * h * w ∈ sec2H E F := by
      have := (mem_normalizer_iff.mp (inv_mem hwH) h).mp hh
      simpa using this
    have h1 := htH _ hh'
    have h2 := (mem_normalizer_iff.mp hwS _).mp h1
    have e : w * (t * (w⁻¹ * h * w) * t⁻¹ * (w⁻¹ * h * w)⁻¹) * w⁻¹ = d * h * d⁻¹ * h⁻¹ := by
      rw [hddef]
      group
    rwa [e] at h2
  have hxH : ∀ h ∈ sec2H E F, x⁻¹ * h * x⁻¹⁻¹ * h⁻¹ ∈ sec2S A R E F := by
    intro h hh
    have := hD.hxH' h⁻¹ (inv_mem hh)
    simpa using this
  have htt : t * t = 1 := ht.sq
  have hdd : d * d = 1 := by
    rw [hddef]
    calc w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hdz : d * z * d⁻¹ = z := by
    rw [hddef]
    calc w * t * w⁻¹ * z * (w * t * w⁻¹)⁻¹ = w * (t * (w⁻¹ * z * w) * t⁻¹) * w⁻¹ := by group
      _ = z := by
          have hw' : w⁻¹ * z * w = z := by
            calc w⁻¹ * z * w = w⁻¹ * (w * z * w⁻¹) * w := by rw [hwz']
              _ = z := by group
          rw [hw', htz, hwz']
  have hdnotS : d ∉ sec2S A R E F := by
    intro h
    apply ht.notS
    have := (mem_normalizer_iff.mp (inv_mem hwS) d).mp h
    rw [hddef] at this
    simpa [mul_assoc] using this
  obtain ⟨T, hT⟩ := C.exists_mat_of_mem hSp hHS hNH ht.normS htH
  obtain ⟨D, hDm⟩ := C.exists_mat_of_mem hSp hHS hNH hdS hdH
  obtain ⟨X, hX⟩ := C.exists_mat_of_mem hSp hHS hNH (inv_mem hx.normS) hxH
  have hTT : matMul T T = matOne := by
    refine C.mat_unique (C.mat_mul ht.normS hT hT) ?_
    rw [htt]
    exact C.mat_one
  have hDD : matMul D D = matOne := by
    refine C.mat_unique (C.mat_mul hdS hDm hDm) ?_
    rw [hdd]
    exact C.mat_one
  have hT1 : T ≠ matOne := by
    intro h
    rw [h] at hT
    apply ht.notS
    refine mem_of_mem_centralizerMod hsylS
      (mem_centralizerMod_of hSp ht.normS (C.mul_inv_mem_of_mat_one hSp ht.normS hT)) (n := 1) ?_
    rw [pow_one, sq]
    exact htt
  have hD1 : D ≠ matOne := by
    intro h
    rw [h] at hDm
    apply hdnotS
    refine mem_of_mem_centralizerMod hsylS
      (mem_centralizerMod_of hSp hdS (C.mul_inv_mem_of_mat_one hSp hdS hDm)) (n := 1) ?_
    rw [pow_one, sq]
    exact hdd
  have hXX : (fun i j => matMul X X i j + X i j + matOne i j) = 0 := by
    refine mat_eq_of_matAct fun m hm1 hm2 => ?_
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    rw [← hsm, matAct_add3, matAct_zero, ← C.mat_mul (inv_mem hx.normS) hX hX s hs, ← hX s hs,
      matAct_matOne]
    have hxs : x⁻¹ * s * x ∈ sec2S A R E F := by
      have := (mem_normalizer_iff.mp (inv_mem hx.normS) s).mp hs
      simpa using this
    have hxxs : x⁻¹ * x⁻¹ * s * x * x ∈ sec2S A R E F := by
      have := (mem_normalizer_iff.mp (inv_mem hx.normS) _).mp hxs
      simpa [mul_assoc] using this
    have h1 := (C.Ψ_eq_zero_iff hSp ((sec2S A R E F).mul_mem ((sec2S A R E F).mul_mem hs hxs)
      hxxs)).mpr (hx.scalar s hs)
    rw [C.Ψ_mul hSp ((sec2S A R E F).mul_mem hs hxs) hxxs, C.Ψ_mul hSp hs hxs] at h1
    have e1 : x⁻¹ * s * x⁻¹⁻¹ = x⁻¹ * s * x := by rw [inv_inv]
    have e2 : x⁻¹ * x⁻¹ * s * (x⁻¹ * x⁻¹)⁻¹ = x⁻¹ * x⁻¹ * s * x * x := by
      rw [mul_inv_rev, inv_inv, ← mul_assoc]
    rw [e1, e2]
    rw [← h1]
    abel
  have hx3 : x ^ 3 = 1 := hx.cube
  have hxx : x⁻¹ * x⁻¹ = x := by
    calc x⁻¹ * x⁻¹ = x ^ 3 * x⁻¹ * x⁻¹ := by rw [hx3, one_mul]
      _ = x := by rw [pow_three]; group
  have hMx : ∀ s ∈ sec2S A R E F, C.Ψ (x * s * x⁻¹) = matAct (matMul X X) (C.Ψ s) := by
    have h1 := C.mat_mul (inv_mem hx.normS) hX hX
    rwa [hxx] at h1
  have hk₁ := C.mat_mul hx.normS (C.mat_mul ht.normS hX hT) hMx
  have hk₂ := C.mat_mul (inv_mem hx.normS) (C.mat_mul ht.normS hMx hT) hX
  obtain ⟨j, rfl⟩ := invol_cases T hTT hT1
  obtain ⟨k, rfl⟩ := invol_cases D hDD hD1
  obtain ⟨i, rfl⟩ := ord3_cases X hXX
  have hzZ1 : z ∈ zpowers z₁ := (hD.hz z hzZ).mp htz
  have hzeq : z = z₁ := by
    rcases hSp.eq_one_or_eq hD.hzZ hzZ1 with h | h
    · exact absurd h hz1
    · exact h
  have hxzZ : x * z * x⁻¹ ∈ sec2Z A E F := (mem_normalizer_iff.mp hx.normZ z).mp hzZ
  have hxz1 : x * z * x⁻¹ ≠ 1 := fun h => hz1 (by
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hxzZ' : x⁻¹ * z * x ∈ sec2Z A E F := by
    have := (mem_normalizer_iff.mp (inv_mem hx.normZ) z).mp hzZ
    simpa using this
  have hxz1' : x⁻¹ * z * x ≠ 1 := fun h => hz1 (by
    calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hdk : ∀ {k' : G} {M : Mat2}, k' ∈ normalizer (sec2S A R E F : Set G) →
      (∀ s ∈ sec2S A R E F, C.Ψ (k' * s * k'⁻¹) = matAct M (C.Ψ s)) → invol k = M →
      d * z * d⁻¹ = k' * z * k'⁻¹ := by
    intro k' M hk' hM hkM
    refine conj_eq_of_conj_mem hSp hk' (fun s hs => ?_) hzZ
    have hds : d * s * d⁻¹ ∈ sec2S A R E F := (mem_normalizer_iff.mp hdS s).mp hs
    have hks : k' * s * k'⁻¹ ∈ sec2S A R E F := (mem_normalizer_iff.mp hk' s).mp hs
    rw [← C.Ψ_eq_iff hSp hds hks, hDm s hs, hM s hs, hkM]
  rcases conj_cases i j k with h | h | h
  ·
    have hTD : ∀ s ∈ sec2S A R E F, C.Ψ (d * s * d⁻¹) = C.Ψ (t * s * t⁻¹) := fun s hs => by
      rw [hDm s hs, hT s hs, h]
    set e := t * d with hedef
    have heS : e ∈ normalizer (sec2S A R E F : Set G) := mul_mem ht.normS hdS
    have heM : ∀ s ∈ sec2S A R E F, C.Ψ (e * s * e⁻¹) = matAct matOne (C.Ψ s) := by
      intro s hs
      rw [C.mat_mul hdS hT hDm s hs, h, hTT]
    have heZ : ∀ c ∈ sec2Z A E F, e * c * e⁻¹ = c := by
      intro c hc
      have h1 := conj_eq_of_conj_mem hSp ht.normS (fun s hs => by
        rw [← C.Ψ_eq_iff hSp ((mem_normalizer_iff.mp hdS s).mp hs)
          ((mem_normalizer_iff.mp ht.normS s).mp hs)]
        exact hTD s hs) hc
      rw [hedef]
      calc t * d * c * (t * d)⁻¹ = t * (d * c * d⁻¹) * t⁻¹ := by group
        _ = t * (t * c * t⁻¹) * t⁻¹ := by rw [h1]
        _ = (t * t) * c * (t * t)⁻¹ := by group
        _ = c := by rw [htt]; group
    have heC : e ∈ centralizerMod (normalizer (sec2S A R E F : Set G)) (sec2S A R E F)
        (sec2Z A E F) := mem_centralizerMod_of hSp heS (C.mul_inv_mem_of_mat_one hSp heS heM)
    have hcentZ : e ∈ centralizer (sec2Z A E F : Set G) := mem_centralizer_iff.mpr fun c hc => by
      calc c * e = e * c * e⁻¹ * e := by rw [heZ c hc]
        _ = e * c := by group
    obtain ⟨e₂, he₂, ⟨n, hn⟩, e₀, he₀, he₀odd, hee⟩ := exists_two_mul_odd_of e
    have he₂S : e₂ ∈ sec2S A R E F := mem_of_mem_centralizerMod hsylS (zpowers_le.mpr heC he₂) hn
    have he₀C := zpowers_le.mpr heC he₀
    have he₀Z : ∀ c ∈ sec2Z A E F, e₀ * c * e₀⁻¹ = c := fun c hc => by
      have h1 : c * e₀ = e₀ * c := mem_centralizer_iff.mp (zpowers_le.mpr hcentZ he₀) c hc
      rw [← h1, mul_inv_cancel_right]
    have he₀SZ : ∀ s ∈ sec2S A R E F, e₀ * s * e₀⁻¹ * s⁻¹ ∈ sec2Z A E F := by
      intro s hs
      have h1 := (inv_mem he₀C).2.2 s hs
      rw [inv_inv] at h1
      have e' : e₀ * s * e₀⁻¹ * s⁻¹ = s * (s⁻¹ * e₀ * s * e₀⁻¹) * s⁻¹ := by group
      rw [e', hSp.conj_Z h1 hs]
      exact h1
    have he₀CS : e₀ ∈ centralizer (sec2S A R E F : Set G) := mem_centralizer_iff.mpr fun s hs => by
      have h1 := mul_conj_eq_of_odd hSp he₀Z he₀SZ he₀odd (pow_orderOf_eq_one e₀) hs
      calc s * e₀ = e₀ * s * e₀⁻¹ * e₀ := by rw [h1]
        _ = e₀ * s := by group
    have he₀T := oddCoreIn_centralizer_le_centralizer_sec2T h4 h34 hE16 h21 h211 h212 hset hT₀2
      (mem_oddCoreIn_centralizer_S h24 h26 hset he₀CS he₀odd)
    have hde : d = t * e₂ * e₀ := by
      calc d = t * (t * d) := by rw [← mul_assoc, htt, one_mul]
        _ = t * (e₂ * e₀) := by rw [← hee]
        _ = t * e₂ * e₀ := by group
    have hte₂T : t * e₂ ∈ sec2T E T₀ := mul_mem htT (hST he₂S)
    have hcomm : e₀ * (t * e₂) = (t * e₂) * e₀ := (mem_centralizer_iff.mp he₀T _ hte₂T).symm
    have he₀sq : e₀ * e₀ ∈ sec2T E T₀ := by
      have h1 : (t * e₂) * (t * e₂) * (e₀ * e₀) = 1 := by
        calc (t * e₂) * (t * e₂) * (e₀ * e₀) = (t * e₂) * (e₀ * (t * e₂)) * e₀ := by
              rw [hcomm]; group
          _ = d * d := by rw [hde]; group
          _ = 1 := hdd
      have h2 : e₀ * e₀ = ((t * e₂) * (t * e₂))⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact inv_mem (mul_mem hte₂T hte₂T)
    have he₀1 : e₀ = 1 := by
      obtain ⟨n', hn'⟩ := hT₀2 ⟨e₀ * e₀, he₀sq.1⟩
      have h1 : (e₀ * e₀) ^ 2 ^ n' = 1 := by simpa using congrArg Subtype.val hn'
      have h2 : orderOf e₀ ∣ 2 ^ (n' + 1) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_succ', pow_mul, sq]
        exact h1
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr he₀odd)) h2)
    have hdt : d = t * e₂ := by rw [hde, he₀1, mul_one]
    have hB : IsQ8Cube (Q.map (MulAut.conj w).toMonoidHom) := isQ8Cube_map hQ.q8 w
    have hyH : y ∈ sec2H E F := hd.uy.2.2.2.1.1.1
    have hyB : y ∈ normalizer ((Q.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
      refine mem_normalizer_map_conj ?_
      have hy' : w⁻¹ * y * w ∈ sec2H E F := by
        have := (mem_normalizer_iff.mp (inv_mem hwH) y).mp hyH
        simpa using this
      exact hQ.HT_le (mem_sup_left hy')
    have hTH' : ∀ τ ∈ Q.map (MulAut.conj w).toMonoidHom, τ ∈ sec2H E F ∨ t * τ ∈ sec2H E F := by
      rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hTH q (hQ.le hq) with hqH | hqH
      · exact Or.inl ((mem_normalizer_iff.mp hwH q).mp hqH)
      · right
        have h1 : w * (t * q) * w⁻¹ ∈ sec2H E F := (mem_normalizer_iff.mp hwH _).mp hqH
        have h2 : t * d = e₂ := by rw [hdt, ← mul_assoc, htt, one_mul]
        have e' : t * (w * q * w⁻¹) = e₂ * (w * (t * q) * w⁻¹) := by
          calc t * (w * q * w⁻¹) = t * (d * d) * (w * q * w⁻¹) := by rw [hdd, mul_one]
            _ = (t * d) * (d * (w * q * w⁻¹)) := by group
            _ = e₂ * (w * (t * q) * w⁻¹) := by rw [h2, hddef]; group
        rw [e']
        exact mul_mem (hSH he₂S) h1
    have heq := QSetting.eq_Q C hD hTH' hyH hd.uy.2.2.2.2 hB le_rfl hyB
    rw [hQeq] at heq
    exact AS76b.mem_normalizer_of_map_conj_eq heq
  · exfalso
    have h1 := hdk (mul_mem (mul_mem (inv_mem hx.normS) ht.normS) hx.normS) hk₁ h
    rw [hdz] at h1
    have h2 : t * (x * z * x⁻¹) * t⁻¹ = x * z * x⁻¹ := by
      calc t * (x * z * x⁻¹) * t⁻¹ = x * ((x⁻¹ * t * x) * z * (x⁻¹ * t * x)⁻¹) * x⁻¹ := by group
        _ = x * z * x⁻¹ := by rw [← h1]
    have h3 : x * z * x⁻¹ ∈ zpowers z₁ := (hD.hz _ hxzZ).mp h2
    rcases hSp.eq_one_or_eq hD.hzZ h3 with h4 | h4
    · exact hxz1 h4
    · exact XData.conj_ne hSp hx hzZ hz1 (h4.trans hzeq.symm)
  · exfalso
    have h1 := hdk (mul_mem (mul_mem hx.normS ht.normS) (inv_mem hx.normS)) hk₂ h
    rw [hdz] at h1
    have h2 : t * (x⁻¹ * z * x) * t⁻¹ = x⁻¹ * z * x := by
      calc t * (x⁻¹ * z * x) * t⁻¹ = x⁻¹ * ((x * t * x⁻¹) * z * (x * t * x⁻¹)⁻¹) * x := by group
        _ = x⁻¹ * z * x := by rw [← h1]
    have h3 : x⁻¹ * z * x ∈ zpowers z₁ := (hD.hz _ hxzZ').mp h2
    rcases hSp.eq_one_or_eq hD.hzZ h3 with h4 | h4
    · exact hxz1' h4
    · apply XData.conj_ne hSp hx hzZ hz1
      calc x * z * x⁻¹ = x * (x⁻¹ * z * x) * x⁻¹ := by rw [h4, hzeq]
        _ = z := by group

end Sec2Q

end CFSG.ComponentClassification.AS81

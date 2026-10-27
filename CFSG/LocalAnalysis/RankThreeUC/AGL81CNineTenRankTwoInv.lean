module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem conj_eq_inv_of_mem_centralizer (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup X}
    (hAn : A.Normal) (hK : IsPGroup p ↥(centralizer (A : Set X)))
    (hmem : ∀ z ∈ centralizer (A : Set X), z ^ p = 1 → z ∈ A) {t : X} (ht : t ^ 2 = 1)
    (htA : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) {c : X} (hc : c ∈ centralizer (A : Set X)) :
    t * c * t⁻¹ = c⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hAn
  let σ : MulAut ↥(centralizer (A : Set X)) := MulAut.conjNormal t
  have hσ2 : ∀ c : ↥(centralizer (A : Set X)), σ (σ c) = c := by
    intro c
    apply Subtype.ext
    simp only [σ, MulAut.conjNormal_apply, Subtype.coe_mk]
    have htt : t * t = 1 := by rw [← pow_two, ht]
    rw [show t * (t * (c : X) * t⁻¹) * t⁻¹ = (t * t) * (c : X) * (t * t)⁻¹ by group,
      htt, one_mul, inv_one, mul_one]
  have hfix : MonoidHom.FixedPointFree σ := by
    intro c hc
    by_contra hc1
    obtain ⟨k, hk⟩ := hK.exists_orderOf_eq_pow c
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hc1 (orderOf_eq_one_iff.mp hk)
    have hpred : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hk0)
    set z : ↥(centralizer (A : Set X)) := c ^ (p ^ (k - 1)) with hzdef
    have hzp : z ^ p = 1 := by
      rw [hzdef, ← pow_mul, ← pow_succ, hpred, ← hk, pow_orderOf_eq_one]
    have hzne : z ≠ 1 := by
      rw [hzdef]
      refine pow_ne_one_of_lt_orderOf (n := p ^ (k - 1)) (pow_ne_zero _ hp.ne_zero) ?_
      rw [hk, ← hpred]
      exact Nat.pow_lt_pow_succ hp.one_lt
    have hfixz : σ z = z := by
      rw [hzdef, map_pow, hc]
    have hzp' : ((z ^ p : ↥(centralizer (A : Set X))) : X) = 1 := by rw [hzp]; rfl
    have hmemA : (z : X) ∈ A := hmem (z : X) z.2 (by simpa using hzp')
    have hconj : t * (z : X) * t⁻¹ = (z : X) := by
      have h := congrArg (Subtype.val) hfixz
      simpa [σ, MulAut.conjNormal_apply] using h
    have hinv : t * (z : X) * t⁻¹ = (z : X)⁻¹ := htA (z : X) hmemA
    have hzsq : (z : X) * (z : X) = 1 :=
      inv_eq_iff_mul_eq_one.mp ((hconj.symm.trans hinv).symm)
    have hdvd2 : orderOf (z : X) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact hzsq
    have hdvdp : orderOf (z : X) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using hzp'
    have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have hone : orderOf (z : X) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvdp hdvd2
    exact hzne (Subtype.ext (by simpa using orderOf_eq_one_iff.mp hone))
  have h2 : σ^[2] = _root_.id := by
    funext c
    exact hσ2 c
  have hinv :=
    MonoidHom.FixedPointFree.coe_eq_inv_of_sq_eq_one (φ := σ) hfix h2
  have hval : σ ⟨c, hc⟩ = (⟨c, hc⟩ : ↥(centralizer (A : Set X)))⁻¹ :=
    congrFun hinv ⟨c, hc⟩
  have := congrArg (Subtype.val) hval
  simpa [σ, MulAut.conjNormal_apply] using this

theorem commute_of_conj_eq_inv {K : Subgroup X} {t : X} (hinv : ∀ c ∈ K, t * c * t⁻¹ = c⁻¹)
    {c d : X} (hc : c ∈ K) (hd : d ∈ K) : c * d = d * c := by
  have h1 : (c * d)⁻¹ = (d * c)⁻¹ := by
    rw [← hinv (c * d) (mul_mem hc hd)]
    calc t * (c * d) * t⁻¹ = (t * c * t⁻¹) * (t * d * t⁻¹) := by group
      _ = c⁻¹ * d⁻¹ := by rw [hinv c hc, hinv d hd]
      _ = (d * c)⁻¹ := by rw [mul_inv_rev]
  exact inv_injective h1

theorem le_commutator_of_conj_eq_inv {V K : Subgroup X} (hVn : V.Normal) {t : X} (htV : t ∈ V)
    (hinv : ∀ c ∈ K, t * c * t⁻¹ = c⁻¹) (hodd : Odd (Nat.card K)) : K ≤ ⁅V, V⁆ := by
  intro c hc
  obtain ⟨j, hj⟩ := hodd
  set d : X := c ^ (j + 1) with hddef
  have hcn : c ^ Nat.card K = 1 := by
    have h : (⟨c, hc⟩ : ↥K) ^ Nat.card K = 1 := pow_card_eq_one'
    have h' := congrArg (Subtype.val) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h'
  have hd2 : d ^ 2 = c := by
    rw [hddef, ← pow_mul]
    rw [show (j + 1) * 2 = Nat.card K + 1 by rw [hj]; ring]
    rw [pow_succ, hcn, one_mul]
  have hdK : d ∈ K := by rw [hddef]; exact K.pow_mem hc (j + 1)
  have hdit : t * d * t⁻¹ = d⁻¹ := hinv d hdK
  have key : d * t * d⁻¹ * t⁻¹ = d * d := by
    have htd : t * d⁻¹ * t⁻¹ = (t * d * t⁻¹)⁻¹ := by group
    calc d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) := by group
      _ = d * (t * d * t⁻¹)⁻¹ := by rw [htd]
      _ = d * d := by rw [hdit, inv_inv]
  have hc_eq : c = d * t * d⁻¹ * t⁻¹ := by
    rw [← hd2, key, pow_two]
  have hcinV : c ∈ V := by
    rw [hc_eq]
    exact V.mul_mem (hVn.conj_mem t htV d) (V.inv_mem htV)
  have hdV : d ∈ V := by rw [hddef]; exact V.pow_mem hcinV (j + 1)
  have hcomm : c = ⁅d, t⁆ := by
    rw [commutatorElement_def]
    exact hc_eq
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator hdV htV

theorem mem_centralizer_of_mem_normalizer_of_card_eq_prime (hp : p.Prime) {B : Subgroup X}
    (hB : Nat.card B = p) {x : X} (hx : x ^ p = 1) (hxN : x ∈ normalizer (B : Set X)) :
    x ∈ centralizer (B : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup X := normalizer (B : Set X)
  have hBN : B ≤ N := Subgroup.le_normalizer
  let y : ↥N := ⟨x, hxN⟩
  let σ : MulAut ↥(B.subgroupOf N) := MulAut.conjNormal y
  have hcard : Nat.card ↥(B.subgroupOf N) = p := by
    have e : ↥(B.subgroupOf N) ≃ ↥B :=
      { toFun := fun z => ⟨z.1.1, z.2⟩
        invFun := fun b => ⟨⟨b, hBN b.2⟩, b.2⟩
        left_inv := by rintro ⟨⟨n, hn⟩, hb⟩; rfl
        right_inv := by rintro ⟨b, hb⟩; rfl }
    rw [Nat.card_congr e, hB]
  haveI : IsCyclic ↥(B.subgroupOf N) := isCyclic_of_prime_card hcard
  have hyp : y ^ p = 1 := by
    apply Subtype.ext
    simpa using hx
  have hσp : σ ^ p = 1 := by
    rw [show σ = MulAut.conjNormal y from rfl, ← map_pow, hyp, map_one]
  have hdvd : orderOf σ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hσp
  have hdvd2 : orderOf σ ∣ Nat.card (MulAut ↥(B.subgroupOf N)) := orderOf_dvd_natCard σ
  rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime hp] at hdvd2
  have hcop : Nat.Coprime p (p - 1) :=
    ((Nat.coprime_self_sub_left hp.one_le).mpr (Nat.coprime_one_left p)).symm
  have hone : orderOf σ = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd2
  have hσ1 : σ = 1 := orderOf_eq_one_iff.mp hone
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hz : σ ⟨⟨b, hBN hb⟩, hb⟩ = ⟨⟨b, hBN hb⟩, hb⟩ := by
    rw [hσ1, MulAut.one_apply]
  have hval := congrArg (fun w : ↥(B.subgroupOf N) => ((w : ↥N) : X)) hz
  have hxb : x * b * x⁻¹ = b := by
    simpa [σ, MulAut.conjNormal_apply, y] using hval
  exact (mul_inv_eq_iff_eq_mul.mp hxb).symm

private theorem conj_pow_eq_of_conj_eq {g b : X} (h : g * b * g⁻¹ = b) (k : ℕ) :
    g * b ^ k * g⁻¹ = b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc g * b ^ (k + 1) * g⁻¹ = (g * b ^ k * g⁻¹) * (g * b * g⁻¹) := by group
        _ = b ^ k * b := by rw [ih, h]
        _ = b ^ (k + 1) := by rw [pow_succ]

private theorem pow_conj_eq_of_conj_eq_mul {g a b : X} (hga : g * a * g⁻¹ = b * a)
    (hgb : g * b * g⁻¹ = b) (k : ℕ) : g ^ k * a * (g ^ k)⁻¹ = b ^ k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hgbk : g * b ^ k * g⁻¹ = b ^ k := conj_pow_eq_of_conj_eq hgb k
      calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹
          = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = g * (b ^ k * a) * g⁻¹ := by rw [ih]
        _ = (g * b ^ k * g⁻¹) * (g * a * g⁻¹) := by group
        _ = b ^ k * (b * a) := by rw [hgbk, hga]
        _ = b ^ (k + 1) * a := by rw [pow_succ]; group

theorem not_le_normalizer_of_card_eq_prime (hp : p.Prime) {A : Subgroup X} (hAn : A.Normal)
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hK : IsPGroup p ↥(centralizer (A : Set X)))
    (hV : ¬ IsPGroup p ↥(closure {x : X | orderOf x = p})) {B : Subgroup X} (hBA : B ≤ A)
    (hB : Nat.card B = p) : ¬ closure {x : X | orderOf x = p} ≤ normalizer (B : Set X) := by
  intro hVB
  haveI := hAn
  let D : Subgroup X :=
    { carrier := {g | (∀ b ∈ B, g * b * g⁻¹ = b) ∧
          ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ B}
      one_mem' := by
        refine ⟨?_, ?_⟩
        · intro b hb; group
        · intro a ha; simpa using B.one_mem
      mul_mem' := by
        rintro g h ⟨hgB, hgA⟩ ⟨hhB, hhA⟩
        refine ⟨?_, ?_⟩
        · intro b hb
          rw [show (g * h) * b * (g * h)⁻¹ = g * (h * b * h⁻¹) * g⁻¹ by group,
            hhB b hb, hgB b hb]
        · intro a ha
          have hca : h * a * h⁻¹ * a⁻¹ ∈ B := hhA a ha
          have hga : g * a * g⁻¹ * a⁻¹ ∈ B := hgA a ha
          have hgc : g * (h * a * h⁻¹ * a⁻¹) * g⁻¹ = h * a * h⁻¹ * a⁻¹ :=
            hgB _ hca
          have hgoal : (g * h) * a * (g * h)⁻¹ * a⁻¹
              = (h * a * h⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) := by
            calc (g * h) * a * (g * h)⁻¹ * a⁻¹
                = g * (h * a * h⁻¹) * g⁻¹ * a⁻¹ := by group
              _ = g * ((h * a * h⁻¹ * a⁻¹) * a) * g⁻¹ * a⁻¹ := by group
              _ = (g * (h * a * h⁻¹ * a⁻¹) * g⁻¹)
                    * (g * a * g⁻¹ * a⁻¹) := by group
              _ = (h * a * h⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) := by rw [hgc]
          rw [hgoal]
          exact B.mul_mem hca hga
      inv_mem' := by
        rintro g ⟨hgB, hgA⟩
        refine ⟨?_, ?_⟩
        · intro b hb
          have hgb : g * b * g⁻¹ = b := hgB b hb
          have h := congrArg (fun z => g⁻¹ * z * g) hgb
          have h2 : g⁻¹ * (g * b * g⁻¹) * g = b := by group
          rw [h2] at h
          simpa only [inv_inv] using h.symm
        · intro a ha
          set a' : X := g⁻¹ * a * g with ha'def
          have ha'A : a' ∈ A := by
            rw [ha'def]; simpa using hAn.conj_mem a ha g⁻¹
          have hga' : g * a' * g⁻¹ = a := by rw [ha'def]; group
          have hmem : a * a'⁻¹ ∈ B := by
            have h := hgA a' ha'A
            rwa [hga'] at h
          have hmem' : a' * a⁻¹ ∈ B := by
            have h := B.inv_mem hmem
            rwa [mul_inv_rev, inv_inv] at h
          simpa only [inv_inv, ha'def] using hmem' }
  have hDp : ∀ g ∈ D, ∃ k, g ^ p ^ k = 1 := by
    intro g hg
    have hgpK : g ^ p ∈ centralizer (A : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hbB : g * a * g⁻¹ * a⁻¹ ∈ B := hg.2 a ha
      have hbA : g * a * g⁻¹ * a⁻¹ ∈ A := hBA hbB
      have hbpow : (g * a * g⁻¹ * a⁻¹) ^ p = 1 := hA.2 _ hbA
      have hga : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
      have hgb : g * (g * a * g⁻¹ * a⁻¹) * g⁻¹ = g * a * g⁻¹ * a⁻¹ :=
        hg.1 _ hbB
      have hstep := pow_conj_eq_of_conj_eq_mul hga hgb p
      have hgp_a : g ^ p * a * (g ^ p)⁻¹ = a := by
        rw [hstep, hbpow, one_mul]
      have h2 : g ^ p * a = a * g ^ p := by
        have h3 := congrArg (fun z => z * g ^ p) hgp_a
        simpa using h3
      exact h2.symm
    obtain ⟨m, hm⟩ := hK ⟨g ^ p, hgpK⟩
    refine ⟨m + 1, ?_⟩
    have hgp' : g ^ (p * p ^ m) = 1 := by
      have hval := congrArg (Subtype.val) hm
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] using hval
    rwa [show p ^ (m + 1) = p * p ^ m by rw [pow_succ, mul_comm]]
  have hSD : {x : X | orderOf x = p} ⊆ D := by
    intro x hx
    have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hxN : x ∈ normalizer (B : Set X) := hVB (Subgroup.subset_closure hx)
    have hxcen : x ∈ centralizer (B : Set X) :=
      mem_centralizer_of_mem_normalizer_of_card_eq_prime hp hB hxp hxN
    have hxcenB : ∀ b ∈ B, x * b * x⁻¹ = b := by
      intro b hb
      have hbx : b * x = x * b := (Subgroup.mem_centralizer_iff.mp hxcen) b hb
      rw [← hbx]; group
    refine ⟨hxcenB, ?_⟩
    intro a ha
    by_cases hxK : x ∈ centralizer (A : Set X)
    · have hax : a * x = x * a := (Subgroup.mem_centralizer_iff.mp hxK) a ha
      have hx_conj : x * a * x⁻¹ = a := by rw [← hax]; group
      rw [hx_conj]
      simpa using B.one_mem
    · have hxK' : ¬ ∀ h ∈ A, h * x = x * h := fun h =>
        hxK (Subgroup.mem_centralizer_iff.mpr h)
      push Not at hxK'
      obtain ⟨a₀, ha₀A, ha₀x⟩ := hxK'
      haveI hcommA : IsMulCommutative ↥A := hA.1
      let α : MulAut ↥A := MulAut.conjNormal x
      have hα_apply : ∀ a : ↥A, ((α a : ↥A) : X) = x * (a : X) * x⁻¹ :=
        fun a => MulAut.conjNormal_apply x a
      let f : ↥A →* ↥A :=
        { toFun := fun a => α a * a⁻¹
          map_one' := by
            change α 1 * (1 : ↥A)⁻¹ = 1
            simp
          map_mul' := by
            intro a b
            rw [map_mul, mul_inv_rev]
            calc α a * α b * (b⁻¹ * a⁻¹)
                = α a * (α b * (b⁻¹ * a⁻¹)) := by group
              _ = α a * ((α b * b⁻¹) * a⁻¹) := by group
              _ = α a * (a⁻¹ * (α b * b⁻¹)) := by
                    rw [mul_comm' (α b * b⁻¹) a⁻¹]
              _ = (α a * a⁻¹) * (α b * b⁻¹) := by group }
      have hBker : B.subgroupOf A ≤ f.ker := by
        intro b hb
        have hbB : (b : X) ∈ B := hb
        have hb_cen : x * (b : X) * x⁻¹ = (b : X) := hxcenB (b : X) hbB
        have hval : ((f b : ↥A) : X) = 1 := by
          change ((α b * b⁻¹ : ↥A) : X) = 1
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hα_apply b, hb_cen, mul_inv_cancel]
        exact Subtype.ext (by simpa using hval)
      have hker_ne_top : f.ker ≠ ⊤ := by
        intro htop
        have hmem : f ⟨a₀, ha₀A⟩ = 1 := by
          have hthis : (⟨a₀, ha₀A⟩ : ↥A) ∈ f.ker := by
            rw [htop]; exact Subgroup.mem_top _
          rwa [MonoidHom.mem_ker] at hthis
        have hαa : α ⟨a₀, ha₀A⟩ = ⟨a₀, ha₀A⟩ := by
          have h' : α ⟨a₀, ha₀A⟩ * (⟨a₀, ha₀A⟩ : ↥A)⁻¹
              = (⟨a₀, ha₀A⟩ : ↥A) * (⟨a₀, ha₀A⟩ : ↥A)⁻¹ := by
            change f ⟨a₀, ha₀A⟩
              = (⟨a₀, ha₀A⟩ : ↥A) * (⟨a₀, ha₀A⟩ : ↥A)⁻¹
            rw [hmem, mul_inv_cancel]
          exact mul_right_cancel h'
        have hxa : a₀ * x = x * a₀ := by
          have h1 := congrArg (Subtype.val) hαa
          rw [hα_apply] at h1
          have h2 := congrArg (fun z => z * x) h1
          have h2' : x * a₀ = a₀ * x := by simpa using h2
          exact h2'.symm
        exact ha₀x hxa
      have hcardA : Nat.card ↥A = p ^ 2 := hAc
      have hBcard : Nat.card ↥(B.subgroupOf A) = p := by
        have e : ↥(B.subgroupOf A) ≃ ↥B :=
          { toFun := fun z => ⟨z.1.1, z.2⟩
            invFun := fun b => ⟨⟨b, hBA b.2⟩, b.2⟩
            left_inv := by rintro ⟨⟨n, hn⟩, hb⟩; rfl
            right_inv := by rintro ⟨b, hb⟩; rfl }
        rw [Nat.card_congr e, hB]
      have hle : p ≤ Nat.card ↥f.ker := by
        rw [← hBcard]
        exact Subgroup.card_le_of_le hBker
      have hkercard : Nat.card ↥f.ker = p := by
        have hpge2 : 2 ≤ p := hp.two_le
        have hdvd : Nat.card ↥f.ker ∣ p ^ 2 := by
          rw [← hcardA]; exact Subgroup.card_subgroup_dvd_card f.ker
        obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
        interval_cases k
        · rw [hk] at hle
          simp at hle
          omega
        · simpa using hk
        · exfalso
          exact hker_ne_top
            (Subgroup.eq_top_of_card_eq (H := f.ker) (by rw [hk, hcardA]))
      have hker_eq : f.ker = B.subgroupOf A :=
        (Subgroup.eq_of_le_of_card_ge hBker (by
          change Nat.card ↥f.ker ≤ Nat.card ↥(B.subgroupOf A)
          rw [hkercard]
          exact le_of_eq hBcard.symm)).symm
      have hindex : f.ker.index = p := by
        have hmul := Subgroup.card_mul_index (f.ker : Subgroup ↥A)
        rw [hkercard, hcardA, pow_two] at hmul
        exact mul_left_cancel₀ hp.ne_zero hmul
      have hrange_card : Nat.card ↥f.range = p := by
        rw [← Subgroup.index_ker f, hindex]
      let R : Subgroup X := f.range.map A.subtype
      have hRcard : Nat.card R = p := by
        change Nat.card (f.range.map A.subtype) = p
        rw [Subgroup.card_map_of_injective (K := f.range) A.subtype_injective, hrange_card]
      have hmemR : ∀ a : ↥A, (f a : X) ∈ R := by
        intro a
        exact Subgroup.mem_map_of_mem A.subtype (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      have hα_map : ∀ a : ↥A, x * (f a : X) * x⁻¹ = (f (α a) : X) := by
        intro a
        have hαf : α (f a) = f (α a) := by
          show α (α a * a⁻¹) = α (α a) * (α a)⁻¹
          rw [map_mul, map_inv]
        calc x * (f a : X) * x⁻¹ = ((α (f a) : ↥A) : X) :=
              (MulAut.conjNormal_apply x (f a)).symm
          _ = (f (α a) : X) := by rw [hαf]
      have hαinv_map : ∀ a : ↥A, x⁻¹ * (f a : X) * x = (f (α.symm a) : X) := by
        intro a
        have hαf : α.symm (f a) = f (α.symm a) := by
          show α.symm (α a * a⁻¹) = α (α.symm a) * (α.symm a)⁻¹
          rw [map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
        calc x⁻¹ * (f a : X) * x = ((α.symm (f a) : ↥A) : X) :=
              (MulAut.conjNormal_symm_apply x (f a)).symm
          _ = (f (α.symm a) : X) := by rw [hαf]
      have hxNR : x ∈ normalizer (R : Set X) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
          obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hz
          rw [← hzy]
          change x * (f b : X) * x⁻¹ ∈ R
          rw [hα_map b]
          exact hmemR (α b)
        · intro hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
          obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hz
          have hy_eq : y = x⁻¹ * (f b : X) * x := by
            have h := congrArg (fun z => x⁻¹ * z * x) hzy
            have h2 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
            rw [h2] at h
            simpa using h.symm
          rw [hy_eq, hαinv_map b]
          exact hmemR (α.symm b)
      have hxcenR : x ∈ centralizer (R : Set X) :=
        mem_centralizer_of_mem_normalizer_of_card_eq_prime hp hRcard hxp hxNR
      have hfker_all : ∀ b : ↥A, f b ∈ f.ker := by
        intro b
        rw [MonoidHom.mem_ker]
        have hxcen_fb : x * (f b : X) * x⁻¹ = (f b : X) := by
          have hcomm := (Subgroup.mem_centralizer_iff.mp hxcenR) (f b : X) (hmemR b)
          rw [← hcomm]; group
        have hval : ((f (f b) : ↥A) : X) = 1 := by
          change ((α (f b) * (f b)⁻¹ : ↥A) : X) = 1
          rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, hxcen_fb,
            mul_inv_cancel]
        exact Subtype.ext (by simpa using hval)
      have hfaB : (f ⟨a, ha⟩ : X) ∈ B := by
        have hmem := hfker_all ⟨a, ha⟩
        rw [hker_eq] at hmem
        exact hmem
      have hfval : (f ⟨a, ha⟩ : X) = x * a * x⁻¹ * a⁻¹ := by
        change ((α ⟨a, ha⟩ * (⟨a, ha⟩ : ↥A)⁻¹ : ↥A) : X) = x * a * x⁻¹ * a⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      rw [← hfval]
      exact hfaB
  have hVD : closure {x : X | orderOf x = p} ≤ D := (Subgroup.closure_le D).mpr hSD
  apply hV
  intro v
  obtain ⟨k, hk⟩ := hDp (v : X) (hVD v.2)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

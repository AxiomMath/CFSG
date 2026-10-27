module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma103
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped MatrixGroups IsMulCommutative

section Psi

variable {H : Type} [CommGroup H]

@[expose] def l113Psi (T : H →* H) : H →* H where
  toFun x := T x * x⁻¹
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, mul_inv_rev]; ac_rfl

theorem l113Psi_apply (T : H →* H) (x : H) : l113Psi T x = T x * x⁻¹ := rfl

theorem l113Psi_cube (T : H →* H) (hT : ∀ x, T (T (T x)) = x) (hc : ∀ x : H, x ^ 3 = 1) (x : H) :
    l113Psi T (l113Psi T (l113Psi T x)) = 1 := by
  have hu : T x * T x * T x = 1 := by simpa [pow_succ] using hc (T x)
  have hv : T (T x) * T (T x) * T (T x) = 1 := by simpa [pow_succ] using hc (T (T x))
  have h2 : l113Psi T (l113Psi T x) = T (T x) * x * (T x)⁻¹ * (T x)⁻¹ := by
    rw [l113Psi_apply, l113Psi_apply, map_mul, map_inv]
    simp only [mul_inv, inv_inv]
    ac_rfl
  rw [h2, l113Psi_apply]
  simp only [map_mul, map_inv, hT, mul_inv, inv_inv]
  calc _ = (x * x⁻¹) * (T x * T x * T x) * (T (T x) * T (T x) * T (T x))⁻¹ := by
          simp only [mul_inv, inv_inv]
          simp only [mul_comm, mul_assoc, mul_left_comm]
    _ = 1 := by simp [hu, hv]

theorem l113_exists_step (T : H →* H) (hT : ∀ x, T (T (T x)) = x) (hc : ∀ x : H, x ^ 3 = 1)
    (S : Subgroup H) (hS : S ≠ ⊤) : ∃ x : H, x ∉ S ∧ l113Psi T x ∈ S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ : ∃ x0 : H, x0 ∉ S := by
    by_contra h
    push Not at h
    exact hS ((Subgroup.eq_top_iff' S).2 h)
  have h1 := hcon x0 hx0
  have h2 := hcon _ h1
  have h3 := hcon _ h2
  rw [l113Psi_cube T hT hc x0] at h3
  exact h3 S.one_mem

theorem l113_card_sup_zpowers {G : Type} [Group G] (S : Subgroup G) {x : G} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hxS : x ∉ S) (hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card (S ⊔ Subgroup.zpowers x : Subgroup G) = 3 * Nat.card S := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcardZ : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  have hxxx : x * x * x = 1 := by simpa [pow_succ] using hx3
  have hinf : Nat.card (S ⊓ Subgroup.zpowers x : Subgroup G) = 1 := by
    have hbot : S ⊓ Subgroup.zpowers x = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hyS, hyZ⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyZ
      have hk' : x ^ (k % (3:ℤ)) = y := by
        have := zpow_mod_orderOf x k
        rw [hord, hk] at *
        simpa using this
      have hmod : k % (3:ℤ) = 0 ∨ k % (3:ℤ) = 1 ∨ k % (3:ℤ) = 2 := by omega
      rcases hmod with h | h | h
      · rw [h, zpow_zero] at hk'
        exact hy1 hk'.symm
      · rw [h, zpow_one] at hk'
        have hxS' : x ∈ S := by rw [hk']; exact hyS
        exact hxS hxS'
      · rw [h, zpow_two] at hk'
        apply hxS
        have hx_eq : x = y * y := by
          rw [← hk']
          calc x = x * (x * x * x) := by rw [hxxx, mul_one]
            _ = x * x * (x * x) := by simp only [mul_assoc]
        rw [hx_eq]
        exact S.mul_mem hyS hyS
    rw [hbot, Subgroup.card_bot]
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hinf, hcardZ, mul_one] at hprod
  rw [hprod, mul_comm]

theorem l113_flag_sup_invariant (T : H →* H) (S : Subgroup H) (hSinv : ∀ s ∈ S, T s ∈ S) {x : H}
    (hpsi : l113Psi T x ∈ S) :
    ∀ s ∈ (S ⊔ Subgroup.zpowers x : Subgroup H), T s ∈ (S ⊔ Subgroup.zpowers x : Subgroup H) := by
  set Y : Subgroup H := S ⊔ Subgroup.zpowers x with hY
  have hTx : T x ∈ Y := by
    have hTx' : T x = l113Psi T x * x := by
      rw [l113Psi_apply, inv_mul_cancel_right]
    rw [hTx']
    exact Y.mul_mem ((le_sup_left : S ≤ Y) hpsi)
      ((le_sup_right : Subgroup.zpowers x ≤ Y) (Subgroup.mem_zpowers x))
  have hle : Y ≤ Y.comap T := by
    apply sup_le
    · intro s hs
      rw [Subgroup.mem_comap]
      exact (le_sup_left : S ≤ Y) (hSinv s hs)
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact hTx
  intro s hs
  exact Subgroup.mem_comap.1 (hle hs)

theorem l113_flag_all [Finite H] (T : H →* H) (hT : ∀ x, T (T (T x)) = x) (hc : ∀ x : H, x ^ 3 = 1) :
    ∀ j : ℕ, 3 ^ j ≤ Nat.card H → ∃ S : Subgroup H, (∀ s ∈ S, T s ∈ S) ∧ Nat.card S = 3 ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨⊥, fun s hs => ?_, by simp⟩
    rw [Subgroup.mem_bot] at hs
    rw [hs, map_one]
    exact Subgroup.one_mem _
  | succ j ih =>
    intro hle
    have hle' : 3 ^ j ≤ Nat.card H :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) hle
    obtain ⟨S, hSinv, hSc⟩ := ih hle'
    have hne : S ≠ ⊤ := by
      intro h
      have h1 : Nat.card H = 3 ^ j := by rw [← Subgroup.card_top, ← h, hSc]
      have h2 : 3 ^ j < 3 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)
      exact absurd (h1 ▸ hle) (not_le.2 h2)
    obtain ⟨x, hxS, hpsi⟩ := l113_exists_step T hT hc S hne
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxS S.one_mem
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set H) := by
      intro g _
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [mul_comm g h, mul_inv_cancel_right]
    refine ⟨S ⊔ Subgroup.zpowers x, l113_flag_sup_invariant T S hSinv hpsi, ?_⟩
    rw [l113_card_sup_zpowers S (hc x) hx1 hxS hnorm, hSc, pow_succ, mul_comm]

theorem l113_count_le [Finite H] (T : H →* H) (hT : ∀ x, T (T (T x)) = x) (hc : ∀ x : H, x ^ 3 = 1) :
    Nat.card H ≤ (Nat.card (l113Psi T).ker) ^ 3 := by
  set F := l113Psi T with hF
  have e1 : Nat.card F.ker * Nat.card F.range = Nat.card H := Subgroup.card_ker_mul_card_range F
  set R := F.range with hR
  have e2 : Nat.card (F.comp R.subtype).ker * Nat.card (F.comp R.subtype).range = Nat.card R :=
    Subgroup.card_ker_mul_card_range (F.comp R.subtype)
  have hk' : Nat.card (F.comp R.subtype).ker ≤ Nat.card F.ker := by
    rw [← Subgroup.card_map_of_injective (f := R.subtype) R.subtype_injective]
    apply Subgroup.card_le_of_le
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hy
    rw [MonoidHom.mem_ker] at hr
    rw [MonoidHom.mem_ker]
    exact hr
  have hr' : Nat.card (F.comp R.subtype).range ≤ Nat.card F.ker := by
    apply Subgroup.card_le_of_le
    intro z hz
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hz
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 y.2
    rw [MonoidHom.mem_ker]
    show F (F y.val) = 1
    rw [← hw]
    exact l113Psi_cube T hT hc w
  calc Nat.card H = Nat.card F.ker * Nat.card F.range := e1.symm
    _ = Nat.card F.ker * (Nat.card (F.comp R.subtype).ker * Nat.card (F.comp R.subtype).range) := by
        rw [e2]
    _ ≤ Nat.card F.ker * (Nat.card F.ker * Nat.card F.ker) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hk' hr')
    _ = (Nat.card F.ker) ^ 3 := by ring

end Psi

section Act

variable {G : Type} [Group G]

@[expose] def l113Act (a : G) (V : Subgroup G) (hV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) : V →* V where
  toFun v := ⟨a * v * a⁻¹, hV v v.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp only [Subgroup.coe_mul, Subtype.coe_mk]; group

theorem l113Act_cube (a : G) (V : Subgroup G) (hV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) (ha3 : a ^ 3 = 1)
    (x : V) : l113Act a V hV (l113Act a V hV (l113Act a V hV x)) = x := by
  ext
  simp only [l113Act, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
  have : a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹ = a ^ 3 * x * (a ^ 3)⁻¹ := by
    rw [pow_three']
    group
  rw [this, ha3]
  simp

theorem l113_isElemAbelian_zpowers {G : Type} [Group G] {a : G} (ha3 : a ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers a) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact zpow_mul_comm a m n
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hm]
    have h3 : a ^ (3:ℤ) = 1 := by simpa using ha3
    calc (a ^ m) ^ 3 = (a ^ m) ^ ((3:ℕ):ℤ) := (zpow_natCast _ 3).symm
      _ = a ^ (m * ((3:ℕ):ℤ)) := (zpow_mul a m _).symm
      _ = a ^ (((3:ℕ):ℤ) * m) := by rw [mul_comm]
      _ = (a ^ ((3:ℕ):ℤ)) ^ m := zpow_mul a _ m
      _ = 1 := by simp [h3]

theorem l113_mem_centralizer_zpowers {G : Type} [Group G] {a c : G} (h : a * c = c * a) :
    c ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact Commute.zpow_left (show Commute a c from h) k

@[expose] def l113Restrict {H : Type} [Group H] (T : H →* H) (S : Subgroup H) (hS : ∀ s ∈ S, T s ∈ S) :
    S →* S where
  toFun s := ⟨T s, hS s s.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end Act

section Ranks

variable {G : Type} [Group G] [Finite G]

theorem l113_pRank_eq {p : ℕ} [hp : Fact p.Prime] {F : Subgroup G} (hF : IsElemAbelian p F) {j : ℕ}
    (hj : Nat.card F = p ^ j) : CFSG.Open.pRank p F = j := by
  apply le_antisymm
  · obtain ⟨E, hEF, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt F
    have h1 : p ^ CFSG.Open.pRank p F ≤ p ^ j := by
      rw [← hEc, ← hj]
      exact Subgroup.card_le_of_le hEF
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h1
  · exact CFSG.SectionRank.le_pRank hp.out.one_lt (le_refl F) hF hj

theorem l113_card_eq_pow_pRank {p : ℕ} [hp : Fact p.Prime] {F : Subgroup G} (hF : IsElemAbelian p F) :
    Nat.card F = p ^ CFSG.Open.pRank p F := by
  obtain ⟨j, hj⟩ := exists_card_eq_pow (isPGroup_of_isElemAbelian' hF)
  rw [l113_pRank_eq hF hj]
  exact hj

end Ranks

section Key

variable {G : Type} [Group G] [Finite G]

theorem l113_ddKey_not_le {p : ℕ} {E A E' A' : Subgroup G}
    (h1 : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p (E' ⊓ A'))
    (h2 : min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A) ≤ min (CFSG.Open.pRank p E') (CFSG.Open.pRank p A'))
    (h3 : CFSG.Open.pRank p E < CFSG.Open.pRank p E') :
    ¬ ddKey p E' A' ≤ ddKey p E A := by
  intro hle
  unfold ddKey at hle
  rcases Prod.Lex.toLex_le_toLex.1 hle with h | ⟨e1, h⟩
  · omega
  · rcases Prod.Lex.toLex_le_toLex.1 h with h' | ⟨e2, h'⟩
    · omega
    · rcases Prod.Lex.toLex_le_toLex.1 h' with h'' | ⟨e3, _⟩
      · omega
      · omega

end Key

variable {G : Type} [Group G] [Finite G]

theorem lemma113_ii_piece0_of_104iv (h104iv : Lemma104_ivStatement) : Lemma113_ii_piece0Statement := by
  intro G _ _ m B M E A a e K Q h E1 hE1M hE1 hrank haN
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDD : IsDDpStar 3 M E A := h.pair
  have hEinD : inD 3 M E := hDD.1.1
  have hAinDp : inDp 3 M A := hDD.1.2.1
  have h2 : 2 ≤ CFSG.Open.pRank 3 (E ⊓ A) := hDD.1.2.2
  have hEsc : IsSCp 3 M E := hEinD.1.1
  have hAsc : IsSCp 3 M A := hAinDp.1.1
  have hEel : IsElemAbelian 3 E := hEsc.2.1
  have hAel : IsElemAbelian 3 A := hAsc.2.1
  have hE4 : CFSG.Open.pRank 3 E = 4 := h.h4
  have hA3 : CFSG.Open.pRank 3 A = 3 := h.h3
  obtain ⟨haA, ha1⟩ := h.ha
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  have haM : a ∈ M := hAsc.1 haA
  haveI : IsMulCommutative E1 := hE1.1
  have hcomm1 : ∀ x ∈ E1, ∀ y ∈ E1, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hnorm1 : ∀ v ∈ E1, a * v * a⁻¹ ∈ E1 := fun v hv => (Subgroup.mem_normalizer_iff.1 haN v).1 hv
  have hT1 : ∀ x : E1, l113Act a E1 hnorm1 (l113Act a E1 hnorm1 (l113Act a E1 hnorm1 x)) = x :=
    fun x => l113Act_cube a E1 hnorm1 ha3 x
  have hc1 : ∀ x : E1, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE1.2 x.1 x.2)
  have hcard1 : 3 ^ 5 ≤ Nat.card E1 := by
    rw [l113_card_eq_pow_pRank hE1]
    exact Nat.pow_le_pow_right (by norm_num) hrank
  obtain ⟨S, hSinv, hSc⟩ := l113_flag_all (l113Act a E1 hnorm1) hT1 hc1 5 hcard1
  set E5 : Subgroup G := S.map E1.subtype with hE5def
  have hE5card : Nat.card E5 = 3 ^ 5 := by
    rw [hE5def, Subgroup.card_map_of_injective E1.subtype_injective, hSc]
  have hE5E1 : E5 ≤ E1 := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hE5el : IsElemAbelian 3 E5 := isElemAbelian_of_le' hE1 hE5E1
  have hE5M : E5 ≤ M := hE5E1.trans hE1M
  set T2 : S →* S := l113Restrict (l113Act a E1 hnorm1) S hSinv with hT2def
  have hT2 : ∀ x : S, T2 (T2 (T2 x)) = x := fun x => Subtype.ext (hT1 x.1)
  have hc2 : ∀ x : S, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hc1 x.1)
  have hcount := l113_count_le T2 hT2 hc2
  rw [hSc] at hcount
  obtain ⟨m, hm5, hmC⟩ : ∃ m, m ≤ 5 ∧ Nat.card (l113Psi T2).ker = 3 ^ m := by
    have hdvd : Nat.card (l113Psi T2).ker ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _
    rw [hSc] at hdvd
    exact (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    rw [hmC] at hcount
    interval_cases m <;> norm_num at hcount
  set C0 := (l113Psi T2).ker with hC0
  let ι : S →* G := E1.subtype.comp S.subtype
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  set Cs : Subgroup G := C0.map ι with hCsdef
  have hCs_card : Nat.card Cs = 3 ^ m := by
    rw [hCsdef, Subgroup.card_map_of_injective hι, hmC]
  have hCs_comm : ∀ c ∈ Cs, a * c = c * a := by
    rintro c ⟨s, hs, rfl⟩
    have h1 : l113Psi T2 s = 1 := (MonoidHom.mem_ker).1 hs
    rw [l113Psi_apply] at h1
    have h2' : T2 s = s := mul_inv_eq_one.1 h1
    have h3 : a * ((s : E1) : G) * a⁻¹ = ((s : E1) : G) := congrArg (fun t : S => ((t : E1) : G)) h2'
    calc a * ((s : E1) : G) = (a * ((s : E1) : G) * a⁻¹) * a := by group
      _ = ((s : E1) : G) * a := by rw [h3]
  have hCs_E5 : Cs ≤ E5 := by
    rintro c ⟨s, _, rfl⟩
    exact ⟨(s : E1), s.2, rfl⟩
  have hCs_E1 : Cs ≤ E1 := hCs_E5.trans hE5E1
  have hCs_el : IsElemAbelian 3 Cs := isElemAbelian_of_le' hE1 hCs_E1
  have hz_el : IsElemAbelian 3 (Subgroup.zpowers a) := l113_isElemAbelian_zpowers ha3
  obtain ⟨X, hXM, hXel, hX27, hCX, haX⟩ :
      ∃ X : Subgroup G, X ≤ M ∧ IsElemAbelian 3 X ∧ 3 ^ 3 ≤ Nat.card X ∧ Cs ≤ X ∧ a ∈ X := by
    by_cases haE1 : a ∈ E1
    · have hE5cent : E5 ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := fun c hc =>
        l113_mem_centralizer_zpowers (hcomm1 a haE1 c (hE5E1 hc))
      refine ⟨E5 ⊔ Subgroup.zpowers a, sup_le hE5M (Subgroup.zpowers_le.2 haM),
        isElemAbelian_sup_of_commute hE5el hz_el hE5cent, ?_,
        (hCs_E5.trans le_sup_left), Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩
      calc 3 ^ 3 ≤ 3 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        _ = Nat.card E5 := hE5card.symm
        _ ≤ Nat.card (E5 ⊔ Subgroup.zpowers a : Subgroup G) := Subgroup.card_le_of_le le_sup_left
    · have hCs_not : a ∉ Cs := fun hh => haE1 (hCs_E1 hh)
      have hnormC : Subgroup.zpowers a ≤ Subgroup.normalizer (Cs : Set G) := by
        rw [Subgroup.zpowers_le]
        apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact (hCs_comm h hh).symm
      have hcardX : Nat.card (Cs ⊔ Subgroup.zpowers a : Subgroup G) = 3 * Nat.card Cs :=
        l113_card_sup_zpowers Cs ha3 ha1 hCs_not hnormC
      have hCs_cent : Cs ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := fun c hc =>
        l113_mem_centralizer_zpowers (hCs_comm c hc)
      refine ⟨Cs ⊔ Subgroup.zpowers a, sup_le (hCs_E1.trans hE1M) (Subgroup.zpowers_le.2 haM),
        isElemAbelian_sup_of_commute hCs_el hz_el hCs_cent, ?_, le_sup_left,
        Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩
      rw [hcardX, hCs_card]
      have hpow : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      norm_num at hpow ⊢
      omega
  obtain ⟨A1, hA1sc, hXA1⟩ := exists_isSCstar_above hXM hXel hX27
  have haA1 : a ∈ A1 := hXA1 haX
  have hA1notD : ¬ inD 3 M A1 := fun hD => h.hna ⟨A1, hD, haA1⟩
  have hA1Dp : inDp 3 M A1 := ⟨hA1sc, fun hU => hA1notD ⟨hA1sc, hU⟩⟩
  have hkEA : CFSG.Open.pRank 3 (E ⊓ A) = 2 := by
    have hEAel : IsElemAbelian 3 (E ⊓ A) := isElemAbelian_of_le' hEel inf_le_left
    have hne : E ⊓ A ≠ A := by
      intro heq
      have hAE : A ≤ E := by
        rw [← heq]
        exact inf_le_left
      have hEA : E = A := hAsc.2.2 E hEsc.1 hEel hAE
      have : CFSG.Open.pRank 3 E = CFSG.Open.pRank 3 A := by rw [hEA]
      omega
    have hlt : Nat.card ((E ⊓ A : Subgroup G)) < Nat.card A := by
      apply lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_right)
      intro hc
      exact hne (Subgroup.eq_of_le_of_card_ge inf_le_right hc.ge)
    have hAc : Nat.card A = 3 ^ 3 := by
      have := l113_card_eq_pow_pRank hAel
      rw [hA3] at this
      exact this
    obtain ⟨j, hj⟩ := exists_card_eq_pow (isPGroup_of_isElemAbelian' hEAel)
    have hjr : CFSG.Open.pRank 3 (E ⊓ A) = j := l113_pRank_eq hEAel hj
    have hj3 : j < 3 := by
      rw [hj, hAc] at hlt
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
    omega
  obtain ⟨R, hR, hE5R⟩ := exists_sylowIn_above hE5M (isPGroup_of_isElemAbelian' hE5el)
  have hEk5 : IsEkIn 3 5 R E5 := ⟨hE5R, hE5el, hE5card⟩
  obtain ⟨-, -, E2, hE2D, hE5E2⟩ := (h104iv h.toSec10Fails hDD hkEA hR).1 E5 hEk5
  have hr5 : 5 ≤ CFSG.Open.pRank 3 E2 :=
    CFSG.SectionRank.le_pRank (by norm_num) hE5E2 hE5el hE5card
  have hr2 : 2 ≤ CFSG.Open.pRank 3 (E2 ⊓ A1) := by
    have hCsEA : Cs ≤ E2 ⊓ A1 := le_inf (hCs_E5.trans hE5E2) (hCX.trans hXA1)
    have := CFSG.SectionRank.le_pRank (by norm_num) hCsEA hCs_el hCs_card
    exact le_trans hm2 this
  have hr3 : 3 ≤ CFSG.Open.pRank 3 A1 := hA1sc.2
  have hmin : min (CFSG.Open.pRank 3 E) (CFSG.Open.pRank 3 A) ≤
      min (CFSG.Open.pRank 3 E2) (CFSG.Open.pRank 3 A1) := by
    rw [hE4, hA3]
    exact le_min (by omega) (by omega)
  have hlt : CFSG.Open.pRank 3 E < CFSG.Open.pRank 3 E2 := by
    rw [hE4]
    omega
  exact l113_ddKey_not_le (p := 3) (by rw [hkEA]; exact hr2) hmin hlt (hDD.2 E2 A1 ⟨hE2D, hA1Dp, hr2⟩)

theorem l113_normal_rank_lt_five {M Q N : Subgroup G} {a : G} (ha : a ∈ Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G))
    (hNQ : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hNM : N ≤ M) (hN : IsElemAbelian 3 N) :
    CFSG.Open.pRank 3 N < 5 := by
  by_contra hlt
  push Not at hlt
  apply h0 N hNM hN hlt
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hNQ a ha h hh
  · intro hh
    have := hNQ a⁻¹ (Q.inv_mem ha) _ hh
    simpa [mul_assoc] using this

theorem lemma113_ii_piece0_of_input31_6 (h31 : Input31_6) : Lemma113_ii_piece0Statement :=
  lemma113_ii_piece0_of_104iv (lemma104_iv_of_input31_6 h31)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Small
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Group
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510ii
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise

structure Input23_25_2Facts : Prop where
  on1 : ∀ (Y : Type) [Group Y] [Finite Y], UniquenessMaximal.IsHatON Y → ∀ B₀ : Subgroup Y,
    IsElemAbelian 3 B₀ → Nat.card B₀ = 27 → ⊤ ≤ gammaLBelow B₀ (⊤ : Subgroup Y)

section Group

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem c25_normal_inner : (MulAut.conj : Y →* MulAut Y).range.Normal where
  conj_mem := by
    rintro _ ⟨y, rfl⟩ φ
    refine ⟨φ y, ?_⟩
    ext z
    simp [MulAut.conj_apply]

omit [Finite Y] in
private theorem c25_conj_eq_one_iff {g : Y} : MulAut.conj g = 1 ↔ g ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut Y => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x).symm

theorem c25_gammaL_to_Y {A : Subgroup (MulAut Y)}
    (hA9 : Nat.card A = 9) (hZ : Nat.card (Subgroup.center Y) = 3)
    (hB₀ : IsElemAbelian 3 (A.comap (MulAut.conj : Y →* MulAut Y)))
    (hB27 : Nat.card (A.comap (MulAut.conj : Y →* MulAut Y)) = 27)
    (hgen : ⊤ ≤ gammaLBelow (A.comap (MulAut.conj : Y →* MulAut Y)) (⊤ : Subgroup Y)) :
    ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
      GLAPLayer 3 (c25Fix S) := by
  set B₀ := A.comap (MulAut.conj : Y →* MulAut Y) with hB₀def
  refine hgen.trans (iSup₂_le fun E hE => ?_)
  obtain ⟨hEB, hrk⟩ := hE
  set S : Subgroup (MulAut Y) := E.map (MulAut.conj : Y →* MulAut Y) with hS
  have hSA : S ≤ A := by
    rintro _ ⟨e, he, rfl⟩
    exact hEB he
  have hfix : (⊤ ⊓ Subgroup.centralizer (E : Set Y) : Subgroup Y) = c25Fix S := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_top, true_and, Subgroup.mem_centralizer_iff,
      mem_c25Fix]
    constructor
    · rintro h _ ⟨e, he, rfl⟩
      simp only [MulAut.conj_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact h e he
    · intro h e he
      have := h _ ⟨e, he, rfl⟩
      simp only [MulAut.conj_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
  have hEel : IsElemAbelian 3 E := c25_isElemAbelian_mono hEB hB₀
  obtain ⟨r, hr⟩ := (c25_isPGroup_of_elemAbelian hEel).exists_card_eq
  have hB3 : CFSG.pRank 3 ↥B₀ = 3 := c25_pRank_eq hB₀ (by rw [hB27]; norm_num)
  have hr2 : 2 ≤ r := by
    have := c25_pRank_eq hEel hr
    rw [hB3, this] at hrk
    omega
  have hE9 : 9 ≤ Nat.card E := by
    rw [hr]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
  let f : ↥E →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp E.subtype
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker ≤ 3 := by
    rw [← hZ]
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, ?_⟩) ?_
    · exact c25_conj_eq_one_iff.1 (MonoidHom.mem_ker.1 x.2)
    · intro x x' h
      have h' : (x.1.1 : Y) = x'.1.1 := congrArg (fun z : ↥(Subgroup.center Y) => (z : Y)) h
      exact Subtype.ext (Subtype.ext h')
  have hmul : Nat.card f.ker * Nat.card S = Nat.card E := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hrange] at h1
    exact h1
  have hS3 : 3 ≤ Nat.card S := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul hker (Nat.le_of_lt_succ hlt)
    omega
  refine le_iSup₂_of_le S ⟨hSA, by omega⟩ ?_
  rw [hfix]

end Group

section Lift

variable {G : Type} [Group G] [Finite G]

theorem c25_exists_three_lift {K B : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) {e : barOf 3 K} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hfix : ∀ (b : G) (hb : b ∈ B), c25Rho hBN ⟨b, hb⟩ e = e) :
    ∃ k : G, ∃ hk : k ∈ K, k ∈ Subgroup.centralizer (B : Set G) ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧
      (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf 3 K) = e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hkC, hkm⟩ := c25_exists_centralized hBN (c25_isPGroup_of_elemAbelian hBel)
    (y := e) (fun b hb => hfix b hb)
  have hn : 0 < orderOf k := orderOf_pos k
  obtain ⟨a, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 3 (by norm_num)
  have hmm : (m * m) % 3 = 1 := by
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h | h <;> simp [Nat.mul_mod, h]
  set k₃ : G := k ^ (m * m) with hk₃
  have hk₃K : k₃ ∈ K := Subgroup.pow_mem _ hk _
  have hk₃C : k₃ ∈ Subgroup.centralizer (B : Set G) := Subgroup.pow_mem _ hkC _
  have hk₃pow : k₃ ^ (3 ^ a) = 1 := by
    rw [hk₃, ← pow_mul]
    have : m * m * 3 ^ a = orderOf k * m := by rw [hnm]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  have hmk : (QuotientGroup.mk (⟨k₃, hk₃K⟩ : ↥K) : barOf 3 K) = e := by
    have h1 : (⟨k₃, hk₃K⟩ : ↥K) = (⟨k, hk⟩ : ↥K) ^ (m * m) := Subtype.ext rfl
    rw [h1, QuotientGroup.mk_pow, hkm]
    obtain ⟨t, ht⟩ : ∃ t, t = m * m := ⟨_, rfl⟩
    rw [← ht] at hmm ⊢
    have : t = 3 * (t / 3) + 1 := by omega
    rw [this, pow_add, pow_mul, he3, one_pow, one_mul, pow_one]
  have hk₃1 : k₃ ≠ 1 := by
    intro h
    apply he1
    rw [← hmk]
    have : (⟨k₃, hk₃K⟩ : ↥K) = 1 := Subtype.ext h
    rw [this]
    exact QuotientGroup.mk_one _
  have hcube : k₃ ^ 3 = 1 := by
    have hK3 : (⟨k₃ ^ 3, Subgroup.pow_mem _ hk₃K 3⟩ : ↥K) ∈ GLAPPrimeCore 3 ↥K := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      have h1 : (⟨k₃ ^ 3, Subgroup.pow_mem _ hk₃K 3⟩ : ↥K) = (⟨k₃, hk₃K⟩ : ↥K) ^ 3 :=
        Subtype.ext rfl
      rw [h1, QuotientGroup.mk_pow, hmk, he3]
    have hxN : k₃ ^ 3 ∈ GLAPPrimeCoreOf 3 K := ⟨_, hK3, rfl⟩
    have hd1 : orderOf (k₃ ^ 3) ∣ 3 ^ a := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm, pow_mul, hk₃pow, one_pow]
    have hd2 : orderOf (k₃ ^ 3) ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
      rw [← Subgroup.orderOf_mk (k₃ ^ 3) hxN]
      exact orderOf_dvd_natCard _
    have hc : Nat.Coprime (3 ^ a) (Nat.card (GLAPPrimeCoreOf 3 K)) :=
      Nat.Coprime.pow_left a (coprime_card_glaPPrimeCoreOf K)
    have := Nat.dvd_gcd hd1 hd2
    rw [hc.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  exact ⟨k₃, hk₃K, hk₃C, hcube, hk₃1, hmk⟩

end Lift

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem c25_isElemAbelian_sup_zpowers {B : Subgroup G} {k : G} (hB : IsElemAbelian 3 B)
    (hk3 : k ^ 3 = 1) (hkC : k ∈ Subgroup.centralizer (B : Set G)) :
    IsElemAbelian 3 (Subgroup.zpowers k ⊔ B) := by
  have hcomm : ∀ u ∈ B, Commute k u := fun u hu => (Subgroup.mem_centralizer_iff.1 hkC u hu).symm
  have hZN : Subgroup.zpowers k ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (B : Set G) hkC
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers k) B hZN
  have hmem : ∀ z ∈ Subgroup.zpowers k ⊔ B, ∃ j ∈ Subgroup.zpowers k, ∃ u ∈ B, z = j * u := by
    intro z hz
    have : z ∈ ((Subgroup.zpowers k : Set G) * (B : Set G)) := by rw [← hset]; exact hz
    obtain ⟨j, hj, u, hu, rfl⟩ := this
    exact ⟨j, hj, u, hu, rfl⟩
  have hjc : ∀ j ∈ Subgroup.zpowers k, ∀ u ∈ B, Commute j u := by
    intro j hj u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hj
    exact (hcomm u hu).zpow_left n
  have hBc := hB.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨j₁, hj₁, u₁, hu₁, ha⟩ := hmem a a.2
    obtain ⟨j₂, hj₂, u₂, hu₂, hb⟩ := hmem b b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [ha, hb]
    have h1 : Commute j₁ j₂ := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hj₁
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hj₂
      exact (Commute.refl k).zpow_zpow n m
    have h2 : Commute u₁ u₂ :=
      congrArg Subtype.val (hBc.is_comm.comm ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩)
    have h3 := hjc j₁ hj₁ u₂ hu₂
    have h4 := hjc j₂ hj₂ u₁ hu₁
    calc j₁ * u₁ * (j₂ * u₂) = j₁ * (u₁ * j₂) * u₂ := by group
      _ = j₁ * (j₂ * u₁) * u₂ := by rw [h4.eq]
      _ = (j₁ * j₂) * (u₁ * u₂) := by group
      _ = (j₂ * j₁) * (u₂ * u₁) := by rw [h1.eq, h2.eq]
      _ = j₂ * (j₁ * u₂) * u₁ := by group
      _ = j₂ * (u₂ * j₁) * u₁ := by rw [h3.eq]
      _ = j₂ * u₂ * (j₁ * u₁) := by group
  · obtain ⟨j, hj, u, hu, rfl⟩ := hmem z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hj
    rw [(hjc _ hj u hu).mul_pow]
    have : (k ^ n) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk3, one_zpow]
    rw [this, hB.2 u hu, one_mul]

theorem input23_25_2_of_facts (hOut : InputOutON) (hSyl : InputSylowON) (F : Input23_25_2Facts) :
    Input23_25_2 := by
  intro G _ _ X K B hK hON hSC hBN hrel
  obtain ⟨hBX, hBel, hmax⟩ := hSC
  set A := c25Img K B with hA
  have hAel : IsElemAbelian 3 A := c25Img_isElemAbelian hBel
  have hcard : Nat.card A = (dQ K).relIndex B := card_c25Img hBN
  obtain ⟨k, hk⟩ := (c25_isPGroup_of_elemAbelian hAel).exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
    have h2 : Nat.card A ≤ 9 := hcard ▸ hrel
    omega
  by_cases hk2' : k = 2
  ·
    have hA9 : Nat.card A = 9 := by rw [hk, hk2']; norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hinnN : (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range.Normal :=
      c25_normal_inner
    have hAinn : A ≤ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range := fun α hα =>
      c25_mem_of_pow_three_of_index _ (hOut _ hON) (hAel.2 α hα)
    have hZ : Nat.card (Subgroup.center (barOf 3 K)) = 3 := hON.2.1
    have hAst : Nat.card (A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K))) = 27 := by
      rw [LocalBalance.Lemma510iiNs.card_comap_conj A hAinn, hZ, hA9]
    have hAstP : IsPGroup 3 ↥(A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K))) :=
      IsPGroup.of_card (n := 3) (by rw [hAst]; norm_num)
    obtain ⟨Qs, hAQ⟩ := hAstP.exists_le_sylow
    have hQ := hSyl _ hON Qs
    have hexp : ∀ g ∈ A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)), g ^ 3 = 1 :=
      fun g hg => congrArg Subtype.val (hQ.2.1 ⟨g, hAQ hg⟩)
    by_cases hab : ∀ x ∈ A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)),
        ∀ y ∈ A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)), x * y = y * x
    · have hel : IsElemAbelian 3 (A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K))) :=
        ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩, hexp⟩
      have hgen := F.on1 _ hON _ hel hAst
      have hY := c25_gammaL_to_Y hA9 hZ hel hAst hgen
      exact c25_transfer hBel hBN (fun X => GLAPLayer 3 X) (fun X => GLAPLayer 3 X)
        (fun X => sSup_le fun L hL => hL.1) (fun E _ => c25_layer_le inf_le_left) hY
    · exfalso
      push Not at hab
      obtain ⟨x, hx, y, hy, hxy⟩ := hab
      set Ast := A.comap (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)) with hAstdef
      set P : Subgroup ↥(Qs : Subgroup (barOf 3 K)) := Ast.subgroupOf Qs with hP
      have hP27 : Nat.card P = 27 := by
        rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv, hAst]
      have hnc : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a :=
        ⟨⟨x, hAQ hx⟩, Subgroup.mem_subgroupOf.2 hx, ⟨y, hAQ hy⟩, Subgroup.mem_subgroupOf.2 hy,
          fun h => hxy (congrArg Subtype.val h)⟩
      obtain ⟨e, hecomm, henot⟩ := c25_exists_centralizer_notin hQ P hP27 hnc
      have he3 : (e : barOf 3 K) ^ 3 = 1 := congrArg Subtype.val (hQ.2.1 e)
      have he1 : (e : barOf 3 K) ≠ 1 := fun h =>
        henot (by
          have : e = 1 := Subtype.ext h
          rw [this]
          exact P.one_mem)
      have hecA : ∀ a ∈ Ast, a * (e : barOf 3 K) = (e : barOf 3 K) * a := fun a ha =>
        congrArg Subtype.val (hecomm ⟨a, hAQ ha⟩ (Subgroup.mem_subgroupOf.2 ha))
      have henotA : (e : barOf 3 K) ∉ Ast := fun h => henot (Subgroup.mem_subgroupOf.2 h)
      have hρA : ∀ (b : G) (hb : b ∈ B), c25Rho hBN ⟨b, hb⟩ ∈ A := fun b hb => by
        rw [hA, ← c25Rho_range hBN]
        exact ⟨⟨b, hb⟩, rfl⟩
      have hfix : ∀ (b : G) (hb : b ∈ B), c25Rho hBN ⟨b, hb⟩ (e : barOf 3 K) = e := by
        intro b hb
        obtain ⟨a, ha⟩ := hAinn (hρA b hb)
        have haA : a ∈ Ast := by
          rw [hAstdef, Subgroup.mem_comap, ha]
          exact hρA b hb
        rw [← ha, MulAut.conj_apply, hecA a haA]
        group
      obtain ⟨k₃, hk₃K, hk₃C, hk₃3, hk₃1, hk₃m⟩ := c25_exists_three_lift hBel hBN he3 he1 hfix
      have hk₃X : k₃ ∈ X := hK.1 hk₃K
      have hk₃B : k₃ ∈ B := by
        have hB'X : Subgroup.zpowers k₃ ⊔ B ≤ X :=
          sup_le (by rw [Subgroup.zpowers_le]; exact hk₃X) hBX
        have hB'el := c25_isElemAbelian_sup_zpowers hBel hk₃3 hk₃C
        have heq := hmax _ hB'X hB'el le_sup_right
        have : k₃ ∈ Subgroup.zpowers k₃ ⊔ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers k₃)
        rwa [heq] at this
      have hconj : (MulAut.conj (e : barOf 3 K) : MulAut (barOf 3 K)) =
          c25Rho hBN ⟨k₃, hk₃B⟩ := by
        ext z
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective z
        rw [c25Rho_apply_mk, MulAut.conj_apply, ← hk₃m]
        rfl
      apply henotA
      rw [hAstdef, Subgroup.mem_comap, hconj]
      exact hρA k₃ hk₃B
  ·
    have hk1 : k ≤ 1 := by omega
    have h3 : Nat.card A ≤ 3 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
    obtain ⟨E, hEB, hrk, J, hJ, hKJ⟩ := c25_small_case hK hBel hBN h3
    have hJle : J ≤ gammaLBelow B K := by
      refine le_trans ?_ (le_iSup₂_of_le E ⟨hEB, hrk⟩ le_rfl)
      exact le_sSup hJ
    exact hKJ.trans (sup_le_sup_right hJle _)

end Main

end CFSG.HardMathSupport.Solomon.Coordinator

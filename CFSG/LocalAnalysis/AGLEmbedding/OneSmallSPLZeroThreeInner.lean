module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup

public section
namespace CFSG.AGLEmbedding

open CFSG.Open

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_fixed_inner_of_coprime {p : ℕ} [Fact p.Prime] {L B E : Subgroup Y}
    (hEp : IsPGroup p E) (hEc : IsMulCommutative E) (hEB : E ≤ B)
    (hEL : E ≤ Subgroup.normalizer (L : Set Y))
    (hcop : ∀ w ∈ L ⊓ B, w ∈ Subgroup.centralizer (L : Set Y) → w ^ p = 1 → w = 1)
    {z : Y} (hzE : z ∈ E) {j : Y} (hj : j ∈ L ⊓ B)
    (hzj : z * j⁻¹ ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ c ∈ L ⊓ B, c ∈ Subgroup.centralizer (E : Set Y) ∧
      z * c⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  classical
  set C := Subgroup.centralizer (L : Set Y) with hC
  set Λ : Subgroup Y := L ⊓ B with hΛ
  have hLC : L ≤ Subgroup.normalizer (C : Set Y) := fun l hl =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hl)
  have hEC : E ≤ Subgroup.normalizer (C : Set Y) := fun a ha =>
    mem_normalizer_centralizer (hEL ha)
  have hEΛ : E ≤ Subgroup.normalizer (Λ : Set Y) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hEL ha, Subgroup.le_normalizer (hEB ha)⟩
  let α : E →* MulAut Λ := Λ.normalizerMonoidHom.comp (Subgroup.inclusion hEΛ)
  have hα : ∀ (a : E) (x : Λ), ((α a x : Λ) : Y) = a * x * (a : Y)⁻¹ := fun _ _ => rfl
  set N : Subgroup Λ := C.subgroupOf Λ with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hLC g.2.1) n).mp hn
    simpa using this⟩
  have hNα : ∀ a : E, ∀ n ∈ N, α a n ∈ N := fun a n hn => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    rw [hα]
    exact (Subgroup.mem_normalizer_iff.mp (hEC a.2) n).mp hn
  have hNcop : ¬ p ∣ Nat.card N := by
    intro hdvd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
    have hw1 : ((w : Λ) : Y) ^ p = 1 := by
      have := pow_orderOf_eq_one w
      rw [hw] at this
      simpa using congrArg (fun x : N => ((x : Λ) : Y)) this
    have hwC : ((w : Λ) : Y) ∈ C := Subgroup.mem_subgroupOf.mp w.2
    have := hcop _ (w : Λ).2 hwC hw1
    have hw' : w = 1 := Subtype.ext (Subtype.ext this)
    rw [hw', orderOf_one] at hw
    exact (Fact.out : p.Prime).one_lt.ne hw
  set jΛ : Λ := ⟨j, hj⟩ with hjΛ
  have hfix : (jΛ : Λ ⧸ N) ∈ {q : Λ ⧸ N |
      ∀ a : E, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα a q = q} := by
    intro a
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq,
      hN, Subgroup.mem_subgroupOf]
    have hza : (a : Y) * z * (a : Y)⁻¹ = z := by
      have := hEc.is_comm.comm a ⟨z, hzE⟩
      have h' : (a : Y) * z = z * a := congrArg Subtype.val this
      rw [h', mul_inv_cancel_right]
    set c₀ := z * j⁻¹ with hc₀
    have hzc : z = c₀ * j := by rw [hc₀, inv_mul_cancel_right]
    have hac₀ : (a : Y) * c₀ * (a : Y)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hEC a.2) c₀).mp hzj
    have hkey : ((α a jΛ : Λ) : Y)⁻¹ * j = j⁻¹ * (c₀⁻¹ * ((a : Y) * c₀ * (a : Y)⁻¹)) * j := by
      rw [hα]
      have : (a : Y) * j * (a : Y)⁻¹ = ((a : Y) * c₀ * (a : Y)⁻¹)⁻¹ * c₀ * j := by
        have h1 : (a : Y) * z * (a : Y)⁻¹ =
            ((a : Y) * c₀ * (a : Y)⁻¹) * ((a : Y) * j * (a : Y)⁻¹) := by rw [hzc]; group
        rw [hza, hzc] at h1
        calc (a : Y) * j * (a : Y)⁻¹ = ((a : Y) * c₀ * (a : Y)⁻¹)⁻¹ *
              (((a : Y) * c₀ * (a : Y)⁻¹) * ((a : Y) * j * (a : Y)⁻¹)) := by group
          _ = ((a : Y) * c₀ * (a : Y)⁻¹)⁻¹ * (c₀ * j) := by rw [← h1]
          _ = ((a : Y) * c₀ * (a : Y)⁻¹)⁻¹ * c₀ * j := by group
      simp only [jΛ]
      rw [this]
      group
    have hmem : ((α a jΛ : Λ) : Y)⁻¹ * j ∈ C := by
      rw [hkey]
      have hjL : j ∈ L := hj.1
      have h1 : c₀⁻¹ * ((a : Y) * c₀ * (a : Y)⁻¹) ∈ C := C.mul_mem (C.inv_mem hzj) hac₀
      have h2 := (Subgroup.mem_normalizer_iff.mp (hLC (L.inv_mem hjL)) _).mp h1
      simpa [mul_assoc] using h2
    simpa using hmem
  rw [CFSG.Semidihedral.Principal.coprime_fixed_point_lifting p hEp α N hNα hNcop] at hfix
  obtain ⟨c, hcfix, hceq⟩ := hfix
  refine ⟨c, c.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, ?_⟩
  · have h := congrArg Subtype.val (hcfix ⟨a, ha⟩)
    rw [hα] at h
    calc a * (c : Y) = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h]
  · have h1 : (c : Λ)⁻¹ * jΛ ∈ N := QuotientGroup.eq.mp hceq
    rw [hN, Subgroup.mem_subgroupOf] at h1
    have h1' : (c : Y)⁻¹ * j ∈ C := by simpa using h1
    have h2 : j * (c : Y)⁻¹ ∈ C := by
      have := (Subgroup.mem_normalizer_iff.mp (hLC c.2.1) _).mp h1'
      simpa [mul_assoc] using this
    have : z * (c : Y)⁻¹ = (z * j⁻¹) * (j * (c : Y)⁻¹) := by group
    rw [this]
    exact C.mul_mem hzj h2

theorem exists_pElem_inf_component {p : ℕ} [Fact p.Prime] {L B E : Subgroup Y}
    (hEp : IsPGroup p E) (hEc : IsMulCommutative E) (hE3 : 3 ≤ CFSG.Open.pRank p E)
    (hB : CFSG.Open.pRank p B ≤ 3) (hEB : E ≤ B) (hEL : E ≤ Subgroup.normalizer (L : Set Y))
    (hcop : ∀ w ∈ L ⊓ B, w ∈ Subgroup.centralizer (L : Set Y) → w ^ p = 1 → w = 1)
    {z : Y} (hzE : z ∈ E) (hzp : z ^ p = 1) (hzL : z ∉ Subgroup.centralizer (L : Set Y))
    {j : Y} (hj : j ∈ L ⊓ B) (hzj : z * j⁻¹ ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ y ∈ E, y ∈ L ∧ y ≠ 1 ∧ y ^ p = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hcLB, hcE, hzc⟩ := exists_fixed_inner_of_coprime hEp hEc hEB hEL hcop hzE hj hzj
  set C := Subgroup.centralizer (L : Set Y) with hC
  have hdvd : p ∣ orderOf c := by
    by_contra hnd
    set d := z * c⁻¹ with hd
    have hzdc : z = d * c := by rw [hd, inv_mul_cancel_right]
    have hdc : d * c = c * d := (Subgroup.mem_centralizer_iff.mp hzc c hcLB.1).symm
    have hzn : z ^ orderOf c = d ^ orderOf c := by
      rw [hzdc, (Commute.mul_pow hdc), pow_orderOf_eq_one, mul_one]
    have hznC : z ^ orderOf c ∈ C := hzn ▸ C.pow_mem hzc _
    have hcopn : Nat.Coprime (orderOf c) p :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopn hp.one_lt
    have hzm : (z ^ orderOf c) ^ m = z := by
      rw [← pow_mul, ← Nat.div_add_mod (orderOf c * m) p, hm, pow_add, pow_mul, hzp, one_pow,
        one_mul, pow_one]
    exact hzL (hzm ▸ C.pow_mem hznC m)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers c) p
    (by rw [Nat.card_zpowers]; exact hdvd)
  have hyp : orderOf (y : Y) = p := by rw [Subgroup.orderOf_coe, hy]
  have hyc : (y : Y) ∈ Subgroup.zpowers c := y.2
  have hyLB : (y : Y) ∈ L ⊓ B := (Subgroup.zpowers_le.mpr hcLB) hyc
  have hyC : (y : Y) ∈ Subgroup.centralizer (E : Set Y) :=
    (Subgroup.zpowers_le.mpr hcE) hyc
  have hy1 : (y : Y) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyp
    exact hp.one_lt.ne hyp
  have hyp' : (y : Y) ^ p = 1 := hyp ▸ pow_orderOf_eq_one _
  have hyE : (y : Y) ∈ E := by
    by_contra hyE
    have h1 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers E hyp' hy1 hyC
      (zpowers_inf_eq_bot_of_not_mem' hp hyp hyE)
    have h2 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (sup_le hEB (Subgroup.zpowers_le.mpr hyLB.2))
    omega
  exact ⟨y, hyE, hyLB.1, hy1, hyp'⟩

theorem exists_mul_pow_of_le_centralizer {X : Subgroup Y} {z : Y}
    (hXz : X ≤ Subgroup.centralizer ({z} : Set Y)) {e : Y}
    (he : e ∈ X ⊔ Subgroup.zpowers z) : ∃ x ∈ X, ∃ m : ℕ, e = x * z ^ m := by
  have hXN : X ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup Y) : Set Y) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hXz hx)).symm
      k)).eq
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN] at he
  obtain ⟨x, hx, w, hw, rfl⟩ := he
  obtain ⟨m, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hw
  exact ⟨x, hx, m, rfl⟩

theorem isElemAbelian_sup_zpowers_of_le_centralizer {p : ℕ} {X : Subgroup Y}
    (hX : IsElemAbelian p X) {z : Y} (hXz : X ≤ Subgroup.centralizer ({z} : Set Y))
    (hzp : z ^ p = 1) : IsElemAbelian p (X ⊔ Subgroup.zpowers z) := by
  have hxz : ∀ x ∈ X, Commute x z := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXz hx)
  have hcomm : ∀ a ∈ X ⊔ Subgroup.zpowers z, ∀ b ∈ X ⊔ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, m, rfl⟩ := exists_mul_pow_of_le_centralizer hXz ha
    obtain ⟨y, hy, n, rfl⟩ := exists_mul_pow_of_le_centralizer hXz hb
    have hxy : Commute x y := congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have h1 : Commute x (y * z ^ n) := hxy.mul_right ((hxz x hx).pow_right n)
    have h2 : Commute (z ^ m) (y * z ^ n) :=
      ((hxz y hy).symm.pow_left m).mul_right (Commute.pow_pow_self z m n)
    exact (h1.mul_left h2).eq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun e he => ?_⟩
  obtain ⟨x, hx, m, rfl⟩ := exists_mul_pow_of_le_centralizer hXz he
  rw [((hxz x hx).pow_right m).mul_pow, hX.2 x hx, one_mul, ← pow_mul, mul_comm, pow_mul, hzp,
    one_pow]

theorem false_of_three_components_scalar {p l : ℕ} [Fact p.Prime] {L : Fin 3 → Subgroup Y}
    (hL : ∀ i, IsComponentOf (L i) ⊤) (hLne : ∀ i j, i ≠ j → L i ≠ L j)
    (hZ : ∀ i, ∀ w ∈ L i, w ∈ Subgroup.centralizer (L i : Set Y) → w ^ p = 1 → w = 1)
    {E X : Subgroup Y} (hEc : IsMulCommutative E) (hXE : X ≤ E) (hXcard : Nat.card X = p ^ 2)
    {z u : Y} (hzE : z ∈ E) (hEz : ∀ e ∈ E, ∃ x ∈ X, ∃ m : ℕ, e = x * z ^ m)
    (hzp : z ^ p = 1) (hzL : ∀ i, z ∉ Subgroup.centralizer (L i : Set Y))
    (huL : ∀ i, u ∈ Subgroup.normalizer (L i : Set Y))
    (huz : u * z = z * u) (hux : ∀ x ∈ X, u * x * u⁻¹ = x ^ l) (hl : Nat.Coprime (l - 1) p)
    (hl0 : 1 ≤ l) (hy : ∀ i, ∃ y ∈ E, y ∈ L i ∧ y ≠ 1 ∧ y ^ p = 1) : False := by
  have hp : p.Prime := Fact.out
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have huC : ∀ i, u ∈ Subgroup.normalizer (Subgroup.centralizer (L i : Set Y) : Set Y) :=
    fun i => mem_normalizer_centralizer (huL i)
  have hKX : ∀ i, ∀ k ∈ E, k ∈ Subgroup.centralizer (L i : Set Y) → k ∈ X := by
    intro i k hkE hkC
    obtain ⟨x, hx, m, rfl⟩ := hEz k hkE
    have hxE := hXE hx
    have hzmE : z ^ m ∈ E := E.pow_mem hzE m
    have hu1 : u * (x * z ^ m) * u⁻¹ = x ^ l * z ^ m := by
      have : u * (x * z ^ m) * u⁻¹ = (u * x * u⁻¹) * (u * z ^ m * u⁻¹) := by group
      rw [this, hux x hx]
      have hzu : u * z ^ m * u⁻¹ = z ^ m := by
        rw [((Commute.pow_right huz m)).eq, mul_inv_cancel_right]
      rw [hzu]
    have hukC : u * (x * z ^ m) * u⁻¹ ∈ Subgroup.centralizer (L i : Set Y) :=
      (Subgroup.mem_normalizer_iff.mp (huC i) _).mp hkC
    have hpow : (x * z ^ m) ^ l = x ^ l * (z ^ m) ^ l :=
      (Commute.mul_pow (hcomm x hxE _ hzmE) l)
    have hw : (z ^ m) ^ (l - 1) ∈ Subgroup.centralizer (L i : Set Y) := by
      have h1 : (x * z ^ m) ^ l * (u * (x * z ^ m) * u⁻¹)⁻¹ ∈
          Subgroup.centralizer (L i : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.pow_mem _ hkC l) (Subgroup.inv_mem _ hukC)
      have h2 : (x * z ^ m) ^ l * (u * (x * z ^ m) * u⁻¹)⁻¹ = (z ^ m) ^ (l - 1) := by
        rw [hpow, hu1]
        have hxl : x ^ l * (z ^ m) ^ l * (x ^ l * z ^ m)⁻¹ = (z ^ m) ^ l * (z ^ m)⁻¹ := by
          have hc2 : x ^ l * (z ^ m) ^ l = (z ^ m) ^ l * x ^ l :=
            hcomm _ (E.pow_mem hxE l) _ (E.pow_mem hzmE l)
          have hc3 : x ^ l * z ^ m = z ^ m * x ^ l := hcomm _ (E.pow_mem hxE l) _ hzmE
          rw [hc2, hc3]
          group
        rw [hxl, ← pow_sub_one_mul (by omega : l ≠ 0) (z ^ m)]
        group
      exact h2 ▸ h1
    obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hl hp.one_lt
    have hzmp : (z ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]
    have hzm1 : ((z ^ m) ^ (l - 1)) ^ n = z ^ m := by
      rw [← pow_mul, ← Nat.div_add_mod ((l - 1) * n) p, hn, pow_add, pow_mul, hzmp, one_pow,
        one_mul, pow_one]
    have hzmC : z ^ m ∈ Subgroup.centralizer (L i : Set Y) :=
      hzm1 ▸ Subgroup.pow_mem _ hw n
    by_cases hz1 : z ^ m = 1
    · rw [hz1, mul_one]
      exact hx
    · exfalso
      apply hzL i
      have hzz : z ∈ Subgroup.zpowers (z ^ m) := by
        have hm : Nat.Coprime m p := by
          rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
          intro hpm
          obtain ⟨q, rfl⟩ := hpm
          exact hz1 (by rw [pow_mul, hzp, one_pow])
        obtain ⟨n', -, hn'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hp.one_lt
        refine Subgroup.mem_zpowers_iff.mpr ⟨(n' : ℤ), ?_⟩
        rw [zpow_natCast, ← pow_mul, ← Nat.div_add_mod (m * n') p, hn', pow_add, pow_mul, hzp,
          one_pow, one_mul, pow_one]
      exact (Subgroup.zpowers_le.mpr hzmC) hzz
  obtain ⟨y₀, hy₀E, hy₀L, hy₀1, hy₀p⟩ := hy 0
  obtain ⟨y₁, hy₁E, hy₁L, hy₁1, hy₁p⟩ := hy 1
  obtain ⟨y₂, hy₂E, hy₂L, hy₂1, hy₂p⟩ := hy 2
  have hcen : ∀ i j, i ≠ j → ∀ y ∈ L i, y ∈ Subgroup.centralizer (L j : Set Y) :=
    fun i j hij y hyL => le_centralizer_of_component_ne (hL i) (hL j) (hLne i j hij) hyL
  set K : Subgroup Y := E ⊓ Subgroup.centralizer (L 2 : Set Y) with hKdef
  have hKX' : K ≤ X := fun k hk => hKX 2 k hk.1 hk.2
  have hy₀K : y₀ ∈ K := ⟨hy₀E, hcen 0 2 (by decide) y₀ hy₀L⟩
  have hy₁K : y₁ ∈ K := ⟨hy₁E, hcen 1 2 (by decide) y₁ hy₁L⟩
  have hy₂X : y₂ ∈ X := hKX 0 y₂ hy₂E (hcen 2 0 (by decide) y₂ hy₂L)
  have hy₂K : y₂ ∉ K := fun h => hy₂1 (hZ 2 y₂ hy₂L h.2 hy₂p)
  have hKXne : K.subgroupOf X ≠ ⊤ := fun h => hy₂K (by
    have : (⟨y₂, hy₂X⟩ : X) ∈ K.subgroupOf X := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this)
  have hKcard : Nat.card K = p := by
    have hdvd : Nat.card (K.subgroupOf X) ∣ p ^ 2 :=
      hXcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hKeq : Nat.card (K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX').toEquiv
    have hk2 : k ≠ 2 := fun h => hKXne (Subgroup.eq_top_of_card_eq _ (by
      rw [hkeq, h, hXcard]))
    have hk0 : k ≠ 0 := fun h => by
      rw [h, pow_zero, hKeq] at hkeq
      have hbot := Subgroup.eq_bot_of_card_eq K hkeq
      exact hy₀1 (by rw [hbot] at hy₀K; exact hy₀K)
    rw [← hKeq, hkeq]
    have : k = 1 := by omega
    rw [this, pow_one]
  have hKz : Subgroup.zpowers y₀ = K := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy₀K)
    rw [hKcard, Nat.card_zpowers, orderOf_eq_prime hy₀p hy₀1]
  have hy₁0 : y₁ ∈ L 0 := (Subgroup.zpowers_le.mpr hy₀L) (hKz ▸ hy₁K)
  exact hy₁1 (hZ 0 y₁ hy₁0 (hcen 1 0 (by decide) y₁ hy₁L) hy₁p)

end CFSG.AGLEmbedding

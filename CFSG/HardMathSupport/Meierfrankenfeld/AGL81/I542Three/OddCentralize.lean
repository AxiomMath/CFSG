module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.Quasithin.Background.B1Offender
public import CFSG.RankThree.FFModules.BinaryTransport

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three

open CFSG CFSG.Quasithin
open scoped commutatorElement

section MulAutWorld

variable {G : Type} [Group G] {V : Type} [CommGroup V]

theorem mem_fixV_map {π : G →* MulAut V} {E : Subgroup G} {u : V} :
    u ∈ fixV (E.map π) ↔ ∀ e ∈ E, π e u = u := by
  rw [mem_fixV]
  constructor
  · intro h e he
    exact h (π e) (Subgroup.mem_map_of_mem _ he)
  · intro h x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    exact h e he

theorem mem_stabSub_fixV_map {π : G →* MulAut V} {E : Subgroup G} {g : G}
    (hg : ∀ e ∈ E, g * e = e * g) : π g ∈ stabSub (fixV (E.map π)) := by
  have key : ∀ e ∈ E, ∀ u : V, π e (π g u) = π g (π e u) := by
    intro e he u
    have := congrArg (fun m : G => π m u) (hg e he).symm
    simpa [map_mul] using this
  intro u
  simp only [mem_fixV_map]
  constructor
  · intro h e he
    apply (π g).injective
    rw [← key e he u]
    exact h e he
  · intro h e he
    rw [key e he u, h e he]

theorem key_commute [Finite G] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (π : G →* MulAut V)
    (hπ : Function.Injective π) {A E R : Subgroup G} (hEA : E ≤ A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hAE : Nat.card A ≤ 2 * Nat.card E)
    (hb : Nat.card E * Nat.card (fixV (E.map π)) ≤ Nat.card A * Nat.card (fixV (A.map π)))
    (hAR : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R)
    {n : ℕ} (hn : Odd n) (hn3 : ¬ 3 ∣ n) (hRn : ∀ r ∈ R, r ^ n = 1)
    {x : G} (hx : x ∈ R) (hxE : ∀ e ∈ E, x * e = e * x) {a : G} (ha : a ∈ A) :
    x * a = a * x := by
  classical
  set U : Subgroup V := fixV (E.map π) with hU
  have haE : ∀ e ∈ E, a * e = e * a := fun e he => hAc a ha e (hEA he)
  have hcardU : Nat.card U ≤ 2 * Nat.card (fixV (A.map π)) := by
    have hEpos : 0 < Nat.card E := Nat.card_pos
    have h1 : Nat.card E * Nat.card U ≤ Nat.card E * (2 * Nat.card (fixV (A.map π))) := by
      calc Nat.card E * Nat.card U ≤ Nat.card A * Nat.card (fixV (A.map π)) := hb
        _ ≤ (2 * Nat.card E) * Nat.card (fixV (A.map π)) := Nat.mul_le_mul_right _ hAE
        _ = Nat.card E * (2 * Nat.card (fixV (A.map π))) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hEpos
  set y : G := x * a * x⁻¹ * a⁻¹ with hy
  have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hA2 a ha)
  have hyR : y ∈ R := by
    have : y = x * (a * x⁻¹ * a⁻¹) := by rw [hy]; group
    rw [this]
    exact R.mul_mem hx (hAR a ha x⁻¹ (R.inv_mem hx))
  have hyE : ∀ e ∈ E, y * e = e * y := by
    intro e he
    have h1 : Commute x e := hxE e he
    have h2 : Commute a e := haE e he
    exact ((((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left)).eq
  have hinv : a * y * a⁻¹ = y⁻¹ := by
    have e1 : y = x * a * x⁻¹ * a := by rw [hy, haa]
    have e2 : y⁻¹ = a * x * a * x⁻¹ := by
      rw [e1]
      simp only [mul_inv_rev, inv_inv, haa, mul_assoc]
    rw [e2, haa, e1]
    calc a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ * (a * a) := by group
      _ = a * x * a * x⁻¹ := by rw [hA2 a ha, mul_one]
  let sa : stabSub U := ⟨π a, mem_stabSub_fixV_map haE⟩
  let sy : stabSub U := ⟨π y, mem_stabSub_fixV_map hyE⟩
  have hsa : sa * sa = 1 := Subtype.ext (by
    show π a * π a = 1
    rw [← map_mul, hA2 a ha, map_one])
  have hsay : sa * sy * sa⁻¹ = sy⁻¹ := Subtype.ext (by
    show π a * π y * (π a)⁻¹ = (π y)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv])
  have hsyn : sy ^ n = 1 := Subtype.ext (by
    show (π y) ^ n = 1
    rw [← map_pow, hRn y hyR, map_one])
  set t : MulAut U := resHom U sa with ht
  set z : MulAut U := resHom U sy with hz
  have htz : t * z * t⁻¹ = z⁻¹ := by
    rw [ht, hz, ← map_inv, ← map_mul, ← map_mul, hsay, map_inv]
  have hzn : z ^ n = 1 := by rw [hz, ← map_pow, hsyn, map_one]
  have hUmem : ∀ v ∈ fixV (A.map π), v ∈ U := by
    intro v hv
    rw [hU, mem_fixV_map]
    rw [mem_fixV_map] at hv
    exact fun e he => hv e (hEA he)
  have hmem : ∀ v (hv : v ∈ fixV (A.map π)),
      (⟨v, hUmem v hv⟩ : U) ∈ fixV (Subgroup.zpowers t) := by
    intro v hv
    have hta : t ⟨v, hUmem v hv⟩ = ⟨v, hUmem v hv⟩ := by
      apply Subtype.ext
      exact mem_fixV_map.1 hv a ha
    have hs : Subgroup.zpowers t ≤ MulAction.stabilizer (MulAut U) (⟨v, hUmem v hv⟩ : U) :=
      Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hta)
    rw [mem_fixV]
    intro s hs'
    have := hs hs'
    rwa [MulAction.mem_stabilizer_iff] at this
  have hfixcard : Nat.card (fixV (A.map π)) ≤ Nat.card (fixV (Subgroup.zpowers t)) :=
    Nat.card_le_card_of_injective
      (fun v => ⟨⟨v.1, hUmem v.1 v.2⟩, hmem v.1 v.2⟩)
      (fun v w h => Subtype.ext (congrArg (fun s => ((s.1 : U) : V)) h))
  have hz1 : z = 1 := by
    by_contra hz1
    have hodd : orderOf z ∣ n := orderOf_dvd_of_pow_eq_one hzn
    by_cases ht1 : t = 1
    · rw [ht1] at htz
      have hzz : z * z = 1 := by
        rw [mul_eq_one_iff_eq_inv]
        simpa using htz
      have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
      have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn
      exact hz1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) hodd))
    · obtain ⟨w, htw⟩ := B1.tv_of_index_two ht1 (by omega)
      have hz3 : z ^ 3 = 1 :=
        (B1.inverted_by_transvection (B1.sq_eq_one_sub hV U) htw ht1 hn hzn hz1 htz).2.2.2
      have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn3
      exact hz1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h3) hodd))
  have hzU : ∀ u ∈ fixV (E.map π), π y u = u := by
    intro u hu
    exact congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : V)) hz1
  have hYodd : Odd (Nat.card (Subgroup.zpowers (π y))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hRn y hyR, map_one]))
  have hB : IsPGroup 2 (E.map π) := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    show (π e) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two, ← map_mul, hA2 e (hEA he), map_one]
  have hcomm : ∀ y' ∈ Subgroup.zpowers (π y), ∀ b ∈ E.map π, y' * b = b * y' := by
    intro y' hy' b hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hb'
    have hc : Commute (π y) (π e) := by
      show π y * π e = π e * π y
      rw [← map_mul, ← map_mul, hyE e he]
    exact (hc.zpow_left k).eq
  have hpy : π y = 1 :=
    B1.eq_one_of_fixes_fixV hV hYodd hB hcomm (Subgroup.mem_zpowers _) hzU
  have hy1 : y = 1 := hπ (by rw [hpy, map_one])
  exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact hy1)

theorem le_centralizer_of_odd [Finite G] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (π : G →* MulAut V) (hπ : Function.Injective π) {A R : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hb : ∀ B ≤ A, Nat.card B * Nat.card (fixV (B.map π)) ≤
      Nat.card A * Nat.card (fixV (A.map π)))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRodd : Odd (Nat.card R))
    (hR3 : ¬ 3 ∣ Nat.card R) : R ≤ Subgroup.centralizer (A : Set G) := by
  obtain ⟨hab, hsq⟩ :=
    CFSG.GH74.Generic.BProg.B2.WeakSigGen.forall_of_isElementaryAbelian hA2
  have hAR' : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun a ha r hr =>
    ((Subgroup.mem_set_normalizer_iff.1 (hAR ha) r).1 hr)
  have hRn : ∀ r ∈ R, r ^ Nat.card R = 1 := fun r hr => by
    have := pow_card_eq_one' (G := R) (x := ⟨r, hr⟩)
    exact congrArg Subtype.val this
  have claim : ∀ E ≤ A, Nat.card A ≤ 2 * Nat.card E →
      ∀ x ∈ R, (∀ e ∈ E, x * e = e * x) → ∀ a ∈ A, x * a = a * x :=
    fun E hEA hAE x hx hxE a ha =>
      key_commute hV π hπ hEA hab hsq hAE (hb E hEA) hAR' hRodd hR3 hRn hx hxE ha
  have hcard : Nat.card ↥A = 2 ^ CFSG.pRank 2 ↥A :=
    CFSG.GH74.Generic.BProg.B2.WeakSigGen.card_eq_two_pow_pRank hA2
  by_cases hr : 2 ≤ CFSG.pRank 2 ↥A
  · refine (CFSG.GH74.Generic.BProg.B2.WeakSigGen.le_iSup_centralizer_hyperplanes hA2 hr hAR
      hRodd).trans (iSup_le fun E => iSup_le fun hEA => iSup_le fun hrank => ?_)
    intro x ⟨hxR, hxE⟩
    have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
      CFSG.GH74.Generic.BProg.B2.WeakSigGen.isElementaryAbelian_of_forall
        (fun u hu v hv => hab u (hEA hu) v (hEA hv)) (fun u hu => hsq u (hEA hu))
    have hcardE : Nat.card ↥E = 2 ^ CFSG.pRank 2 ↥E :=
      CFSG.GH74.Generic.BProg.B2.WeakSigGen.card_eq_two_pow_pRank hEel
    have hAE : Nat.card A ≤ 2 * Nat.card E := by
      rw [hcard, hcardE]
      calc 2 ^ CFSG.pRank 2 ↥A ≤ 2 ^ (CFSG.pRank 2 ↥E + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * 2 ^ CFSG.pRank 2 ↥E := by ring
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (claim E hEA hAE x hxR (fun e he => (Subgroup.mem_centralizer_iff.1 hxE e he).symm) a
      ha).symm
  · have hA : Nat.card A ≤ 2 := by
      rw [hcard]
      calc 2 ^ CFSG.pRank 2 ↥A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (claim ⊥ bot_le (by rw [Subgroup.card_bot]; exact hA) x hx
      (fun e he => by rw [Subgroup.mem_bot.1 he]; simp) a ha).symm

end MulAutWorld

section RepWorld

open CFSG.RankThree.FFModules

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem commutator_eq_bot_of_odd_of_not_three_dvd {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ) {A R : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hb : CFSG.RankThree.FFModules.IsBestOffender ρ A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRodd : Odd (Nat.card R))
    (hR3 : ¬ 3 ∣ Nat.card R) : ⁅R, A⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine le_centralizer_of_odd multiplicative_sq (repMulAut ρ) (repMulAut_injective hρ) hA2 ?_
    hAR hRodd hR3
  intro B hBA
  rw [← card_fixSub_eq_card_fixV_map, ← card_fixSub_eq_card_fixV_map]
  exact hb B hBA

end RepWorld

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three

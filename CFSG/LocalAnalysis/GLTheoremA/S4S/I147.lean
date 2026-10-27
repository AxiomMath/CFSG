module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

private theorem i147_exists_component_ne_bot {H : Type} [Group H] [Finite H] {p : ℕ}
    {X : Subgroup H} (h : GLAPLayer p X ≠ ⊥) :
    ∃ K : Subgroup H, GLAPComponent p X K ∧ K ≠ ⊥ := by
  by_contra hne
  push Not at hne
  apply h
  unfold GLAPLayer
  exact le_bot_iff.1 (sSup_le fun K hK => le_of_eq (hne K hK))

private theorem i147_map_centralizer {H S : Type} [Group H] [Group S] [Finite H] {p : ℕ}
    (hp : p.Prime) (ψ : H →* S) (hψ : Function.Surjective ψ) {a : H} (ha : a ^ p = 1)
    (hcop : Nat.Coprime p (Nat.card ψ.ker)) :
    (Subgroup.centralizer ({a} : Set H)).map ψ = Subgroup.centralizer ({ψ a} : Set S) := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx']
  · intro hs
    obtain ⟨w, rfl⟩ := hψ s
    have hs' : ψ w * ψ a = ψ a * ψ w := Subgroup.mem_centralizer_singleton_iff.1 hs
    have hw : a * w * a⁻¹ * w⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [← hs']
      group
    obtain ⟨x, hxw, hax⟩ :=
      CFSG.SignalizerFunctorTheorem.exists_fixed_of_coprime hp ha ψ.ker hcop hw
    refine ⟨x, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hax).symm
    · have h1 : ψ (x * w⁻¹) = 1 := MonoidHom.mem_ker.1 hxw
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1

private theorem i147_lift_elemAbelian {H S : Type} [Group H] [Group S] [Finite H]
    {ψ : H →* S} (hψ : Function.Surjective ψ) (hO : ¬ 3 ∣ Nat.card ψ.ker)
    {E : Subgroup S} (hE : IsElemAbelian 3 E) :
    ∃ R : Subgroup H, IsElemAbelian 3 R ∧ R.map ψ = E ∧ Nat.card R = Nat.card E := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hOn : ψ.ker.Normal := inferInstance
  have hNO : (⊤ : Subgroup H) ≤ Subgroup.normalizer (ψ.ker : Set H) :=
    (Subgroup.normalizer_eq_top_iff.2 hOn).ge
  have hOE : ψ.ker ≤ E.comap ψ := fun x hx => Subgroup.mem_comap.2 (by
    rw [MonoidHom.mem_ker.1 hx]
    exact E.one_mem)
  have hEp : ∀ e ∈ E.comap ψ, ∃ k : ℕ, e ^ (3 ^ k) ∈ ψ.ker := fun e he =>
    ⟨1, by
      rw [pow_one, MonoidHom.mem_ker, map_pow]
      exact hE.2 _ (Subgroup.mem_comap.1 he)⟩
  have hbot : IsPGroup 3 (⊥ : Subgroup H) := fun x =>
    ⟨0, Subtype.ext (by simp [Subgroup.mem_bot.1 x.2])⟩
  obtain ⟨W, -, hWp, -, hWsup⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_pGroup_lift hp hO hOE
    (le_top.trans hNO) hEp hbot bot_le bot_le hNO (le_sup_of_le_left le_top)
  have hWO : W ⊓ ψ.ker = ⊥ := by
    have hc : Nat.card (W ⊓ ψ.ker : Subgroup H) ∣ Nat.card ψ.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hWp.to_le inf_le_left)
    rw [hj] at hc
    have hj0 : j = 0 := by
      by_contra hne
      exact hO ((dvd_pow_self 3 hne).trans hc)
    exact Subgroup.eq_bot_of_card_eq (W ⊓ ψ.ker) (by rw [hj, hj0, pow_zero])
  have hWinj : ∀ u ∈ W, ∀ v ∈ W, ψ u = ψ v → u = v := by
    intro u hu v hv huv
    have h1 : u⁻¹ * v ∈ W ⊓ ψ.ker :=
      Subgroup.mem_inf.2 ⟨W.mul_mem (W.inv_mem hu) hv, MonoidHom.mem_ker.2 (by
        rw [map_mul, map_inv, huv, inv_mul_cancel])⟩
    rw [hWO, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.1 h1
  have hOmap : ψ.ker.map ψ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
    exact MonoidHom.mem_ker.1 hk
  have hWmap : W.map ψ = E := by
    have h1 := Subgroup.map_comap_eq_self_of_surjective hψ E
    rw [← hWsup, Subgroup.map_sup, hOmap, sup_bot_eq] at h1
    exact h1
  have hinjS : Function.Injective (ψ.subgroupMap W) := by
    intro a b hab
    apply Subtype.ext
    apply hWinj _ a.2 _ b.2
    exact congrArg Subtype.val hab
  have hcardW : Nat.card W = Nat.card (W.map ψ) :=
    Nat.card_congr (Equiv.ofBijective (ψ.subgroupMap W)
      ⟨hinjS, MonoidHom.subgroupMap_surjective ψ W⟩)
  rw [hWmap] at hcardW
  have hWmem : ∀ x ∈ W, ψ x ∈ E := fun x hx => hWmap ▸ Subgroup.mem_map_of_mem ψ hx
  refine ⟨W, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, hWmap, hcardW⟩
  · apply Subtype.ext
    apply hWinj _ (W.mul_mem a.2 b.2) _ (W.mul_mem b.2 a.2)
    rw [map_mul, map_mul]
    have h2 := congrArg Subtype.val
      (hE.1.is_comm.comm (⟨ψ a, hWmem a a.2⟩ : E) ⟨ψ b, hWmem b b.2⟩)
    simpa using h2
  · apply hWinj _ (W.pow_mem hx 3) _ W.one_mem
    rw [map_pow, map_one]
    exact hE.2 _ (hWmem x hx)

theorem i147At_of {G : Type} [Group G] [Finite G] (h : KD147) : I147At G := by
  intro Y L₀ hL hcat
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hcenKD, hE9KD, hcompKD⟩ := h (PSimple 3 L₀) hcat
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L₀) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hZ : Subgroup.center (PQuot 3 L₀) = ⊥ :=
    hcenKD (PQuot 3 L₀) hq (I2611.isPGroup_center_pQuot' hp L₀) ⟨MulEquiv.refl _⟩
  let ψ : ↥L₀ →* PSimple 3 L₀ :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 L₀))).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L₀))
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 L₀)) y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L₀) m
    exact ⟨x, rfl⟩
  have hψker : ∀ x : ↥L₀, ψ x = 1 → x ∈ GLAPPrimeCore 3 ↥L₀ := by
    intro x hx
    have h1 : (QuotientGroup.mk (QuotientGroup.mk x : PQuot 3 L₀) : PSimple 3 L₀) = 1 := hx
    rw [QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hkerN : ψ.ker ≤ GLAPPrimeCore 3 ↥L₀ := fun x hx => hψker x (MonoidHom.mem_ker.1 hx)
  have hcop0 : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥L₀)) := CFSG.pPrimeCore_coprime_card
  have hcop : Nat.Coprime 3 (Nat.card ψ.ker) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hkerN) hcop0
  have hndvd : ¬ 3 ∣ Nat.card ψ.ker := (Nat.Prime.coprime_iff_not_dvd hp).1 hcop
  refine ⟨?_, ?_, hZ⟩
  ·
    obtain ⟨E, hE, hEcard⟩ := hE9KD
    obtain ⟨R, hR, -, hRcard⟩ := i147_lift_elemAbelian hψsurj hndvd hE
    refine ⟨R.map L₀.subtype, Subgroup.map_subtype_le _,
      CFSG.Open.IsElemAbelian.map hR L₀.subtype, ?_⟩
    rw [Subgroup.card_map_of_injective L₀.subtype_injective, hRcard, hEcard]
  ·
    intro z hzL hz3 hz1
    obtain ⟨z', hz'⟩ : ∃ z' : ↥L₀, (z' : G) = z := ⟨⟨z, hzL⟩, rfl⟩
    have hz'3 : z' ^ 3 = 1 := Subtype.ext (by simpa [hz'] using hz3)
    have hz'1 : z' ≠ 1 := fun e => hz1 (by simpa [hz'] using congrArg Subtype.val e)
    have hz'ord : orderOf z' = 3 := orderOf_eq_prime hz'3 hz'1
    have hz'N : z' ∉ GLAPPrimeCore 3 ↥L₀ := by
      intro hmem
      have h1 := orderOf_dvd_natCard (⟨z', hmem⟩ : ↥(GLAPPrimeCore 3 ↥L₀))
      rw [Subgroup.orderOf_mk, hz'ord] at h1
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop0 h1
    have hψz3 : ψ z' ^ 3 = 1 := by rw [← map_pow, hz'3, map_one]
    have hψz1 : ψ z' ≠ 1 := fun e => hz'N (hψker z' e)
    have hψord : orderOf (ψ z') = 3 := orderOf_eq_prime hψz3 hψz1
    obtain ⟨K', hK'c, hK'ne⟩ := i147_exists_component_ne_bot (hcompKD (ψ z') hψord)
    have hK'' : GLAPComponent 3 ((Subgroup.centralizer ({z'} : Set ↥L₀)).map ψ) K' := by
      rw [i147_map_centralizer hp ψ hψsurj hz'3 hcop]
      exact hK'c
    have hkerA : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer ({z'} : Set ↥L₀) ⊓ ψ.ker)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hcop
    obtain ⟨K, hK, hKmap⟩ := exists_glaPComponent_map_eq hp ψ hkerA hK''
    have hKne : K ≠ ⊥ := fun e => hK'ne (by rw [← hKmap, e, Subgroup.map_bot])
    have hkerι : Nat.Coprime 3
        (Nat.card ↥(Subgroup.centralizer ({z'} : Set ↥L₀) ⊓ L₀.subtype.ker)) := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 L₀.subtype_injective, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right 3
    have hKι := glaPComponent_map hp L₀.subtype (A := Subgroup.centralizer ({z'} : Set ↥L₀))
      hkerι hK
    have hAmap : (Subgroup.centralizer ({z'} : Set ↥L₀)).map L₀.subtype =
        L₀ ⊓ Subgroup.centralizer ({z} : Set G) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : x * z' = z' * x := Subgroup.mem_centralizer_singleton_iff.1 hx
        rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
        refine ⟨x.2, ?_⟩
        have := congrArg Subtype.val hx'
        simpa [hz'] using this
      · intro hg
        rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hg
        refine ⟨⟨g, hg.1⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
        apply Subtype.ext
        simpa [hz'] using hg.2
    rw [hAmap] at hKι
    intro hbot
    have hle : K.map L₀.subtype ≤ GLAPLayer 3 (L₀ ⊓ Subgroup.centralizer ({z} : Set G)) :=
      le_sSup hKι
    rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L₀.subtype_injective] at hle
    exact hKne hle

end CFSG.LocalAnalysis.GLTheoremA

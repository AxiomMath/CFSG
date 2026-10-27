module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Asm
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248

theorem noComp1248_of_F4 (hX : HypX1248_F4) (hT : Comp1248Type_F4) (hL : Comp1248Lift_F4) :
    NoComp1248_F4 := by
  intro G _ _ T L V U hS K hK
  obtain ⟨hnotY, -, ⟨p, hp, hpsl⟩, -, hCK⟩ := hT G T L V U hS K hK
  rcases hX G T L V U hS with ⟨X, hXLU, hX3, hXC, l, hl, hlU, hl2⟩ | hY
  · obtain ⟨hK0, huniq⟩ := hL G T L V U hS X hXLU hX3 hXC l hl hlU hl2 K hK ⟨p, hp, hpsl⟩
    have hlU₀ : CFSG.conjugate (U ⊓ conjSubgroup U l) l = U ⊓ conjSubgroup U l := by
      ext x
      rw [QuasithinUnique.BenderBranch.mem_conjugate_iff, Subgroup.mem_inf, Subgroup.mem_inf,
        mem_conjSubgroup_iff, mem_conjSubgroup_iff]
      have h2 := Subgroup.mem_normalizer_iff.1 hl2 x
      have e : l * (l * x * l⁻¹) * l⁻¹ = l ^ 2 * x * (l ^ 2)⁻¹ := by
        rw [sq, mul_inv_rev]
        simp only [mul_assoc]
      rw [e, ← h2]
      exact and_comm
    have hK' := E6.isComponentIn_conjugate' hK0 l
    rw [hlU₀] at hK'
    have h3 : 3 ∣ Nat.card ↥(CFSG.conjugate K l) := by
      rw [CFSG.conjugate,
        Subgroup.card_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
          (MulAut.conj l⁻¹).injective]
      exact S1248.three_dvd_card_psl2 hpsl
    have hKl : CFSG.conjugate K l = K := huniq _ hK' h3
    have hKUl : K ≤ Subgroup.centralizer ((conjSubgroup U l : Subgroup G) : Set G) := by
      have := (E6.isComponentIn_conjugate' hK l).1
      rw [hKl] at this
      exact this
    have hUl_le : conjSubgroup U l ≤ U := by
      have hle : conjSubgroup U l ≤ V ⊓ Subgroup.centralizer (K : Set G) := by
        refine le_inf ?_ (Subgroup.le_centralizer_iff.mp hKUl)
        intro x hx
        rw [mem_conjSubgroup_iff] at hx
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hl.1)
          (l * x * l⁻¹)).1 (hS.le hx)
        have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
        rwa [e] at h1
      rwa [hCK] at hle
    have hcard : Nat.card ↥(conjSubgroup U l) = Nat.card ↥U := by
      rw [conjSubgroup,
        Subgroup.card_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
          (MulAut.conj l⁻¹).injective]
    have heq : conjSubgroup U l = U := Subgroup.eq_of_le_of_card_ge hUl_le hcard.ge
    exact hlU (QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq)
  · exact hnotY hY

theorem oddCore1248_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (hInv : OddInv1248_F4) (hE : OddCentE1248_F4) (hQ : OddCentQ1248_F4)
    (hF : OddFinal1248_F4) :
    OddCore1248_F4 := by
  intro G _ _ T L V U hS
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hS.cx hS.quot
  have hzVL : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hf.zV]
    exact Subgroup.mem_zpowers z
  have hz1 : z ≠ 1 := by
    intro h
    have := hf.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hoddO : ∀ W : Subgroup G,
      ∀ x ∈ QuasithinUnique.oddCoreIn (Subgroup.centralizer (W : Set G)), Odd (orderOf x) :=
    fun W x hx => Odd.of_dvd_nat (QuasithinUnique.odd_card_oddCoreIn _)
      (Subgroup.orderOf_dvd_natCard _ hx)
  have hsub : ∀ U' : Subgroup G, Setting G T L V U' → ∀ U₀ : Subgroup G, U₀ ≤ U' →
      U₀.relIndex U' = 2 → QuasithinUnique.oddCoreIn (Subgroup.centralizer (U' : Set G)) ≤
        QuasithinUnique.oddCoreIn (Subgroup.centralizer (U₀ : Set G)) := by
    intro U' hS' U₀ hU₀ hidx
    refine S1248.le_oddCoreIn_of_centralizes
      ((QuasithinUnique.oddCoreIn_le _).trans (Subgroup.centralizer_le hU₀)) (hoddO U')
      (hQ G T L V U' hS' U₀ hU₀ hidx) ?_ (hE G T L V U' hS' U₀ hU₀ hidx)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxH : x ∈ Subgroup.centralizer (U₀ : Set G) :=
      Subgroup.centralizer_le hU₀ (QuasithinUnique.oddCoreIn_le _ hx)
    have hxy : x * y * x⁻¹ ∈ QuasithinUnique.oddCoreIn (Subgroup.centralizer (U₀ : Set G)) :=
      (Subgroup.mem_normalizer_iff.1 (QuasithinUnique.le_normalizer_oddCoreIn _ hxH) y).1 hy
    have hinvU' := hInv G T L V U' hS' z hzVL hz1 U' (Or.inl rfl)
    have hinvU₀ := hInv G T L V U' hS' z hzVL hz1 U₀ (Or.inr ⟨hU₀, hidx⟩)
    exact (S1248.commute_of_inverts (hinvU' x hx) (hinvU₀ y hy) (hinvU₀ _ hxy)
      (hoddO U' x hx)).symm
  have hMV : ∀ m ∈ Subgroup.normalizer (L : Set G), m ∈ Subgroup.normalizer (V : Set G) :=
    fun m hm => by rw [← hf.MN]; exact hm
  have hmapV : ∀ m ∈ Subgroup.normalizer (L : Set G), V.map (MulAut.conj m).toMonoidHom = V := by
    intro m hm
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hMV m hm)) x
    rw [inv_inv] at h
    exact h.symm
  have hconjS : ∀ m ∈ Subgroup.normalizer (L : Set G),
      Setting G T L V (U.map (MulAut.conj m).toMonoidHom) := by
    intro m hm
    refine ⟨hS.cx, hS.quot, ?_, ?_, ?_⟩
    · rw [← hmapV m hm]
      exact Subgroup.map_mono hS.le
    · rw [← hmapV m hm, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj m).injective]
      exact hS.hyper
    · intro hle
      apply hS.escape
      intro c hc
      have hc' : m * c * m⁻¹ ∈ Subgroup.centralizer
          ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨u, hu, rfl⟩
        have := Subgroup.mem_centralizer_iff.1 hc u hu
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc m * u * m⁻¹ * (m * c * m⁻¹) = m * (u * c) * m⁻¹ := by group
          _ = m * (c * u) * m⁻¹ := by rw [this]
          _ = m * c * m⁻¹ * (m * u * m⁻¹) := by group
      have h1 := hle hc'
      have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMV m hm)) h1)
        (hMV m hm)
      simpa [mul_assoc] using h2
  set O := QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) with hOdef
  have hOconj : ∀ m : G, O.map (MulAut.conj m).toMonoidHom ≤ QuasithinUnique.oddCoreIn
      (Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) := by
    intro m
    have hCm : Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
        (Subgroup.centralizer (U : Set G)).map (MulAut.conj m).toMonoidHom := by
      ext c
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_centralizer_iff,
        Subgroup.mem_centralizer_iff]
      constructor
      · intro h u hu
        have := h (m * u * m⁻¹) ⟨u, hu, by simp [MulAut.conj_apply]⟩
        calc u * (m⁻¹ * c * m) = m⁻¹ * ((m * u * m⁻¹) * c) * m := by group
          _ = m⁻¹ * (c * (m * u * m⁻¹)) * m := by rw [this]
          _ = m⁻¹ * c * m * u := by group
      · rintro h _ ⟨u, hu, rfl⟩
        have := h u hu
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc m * u * m⁻¹ * c = m * (u * (m⁻¹ * c * m)) * m⁻¹ := by group
          _ = m * ((m⁻¹ * c * m) * u) * m⁻¹ := by rw [this]
          _ = c * (m * u * m⁻¹) := by group
    rw [hCm]
    refine QuasithinUnique.DoubleA3.le_oddCoreIn_of_odd (Subgroup.map_mono
      (QuasithinUnique.oddCoreIn_le _)) ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨c * y * c⁻¹, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        exact (Subgroup.mem_normalizer_iff.1 (QuasithinUnique.le_normalizer_oddCoreIn _ hc) y).1
          hy
      · rintro ⟨y, hy, hyx⟩
        refine ⟨c⁻¹ * y * c, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.1
            (QuasithinUnique.le_normalizer_oddCoreIn _ (Subgroup.inv_mem _ hc)) y).1 hy
          simpa using this
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx ⊢
          have hx : x = (m * c * m⁻¹)⁻¹ * (m * y * m⁻¹) * (m * c * m⁻¹) := by
            rw [hyx]
            group
          rw [hx]
          group
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj m).toMonoidHom)
        (MulAut.conj m).injective]
      exact QuasithinUnique.odd_card_oddCoreIn _
  have hinvU := hInv G T L V U hS z hzVL hz1 U (Or.inl rfl)
  have hcommOm : ∀ m ∈ Subgroup.normalizer (L : Set G), ∀ a ∈ O,
      ∀ b ∈ O.map (MulAut.conj m).toMonoidHom, a * b = b * a := by
    intro m hm a ha b hb
    by_cases hmU : U.map (MulAut.conj m).toMonoidHom = U
    · have hb' := hOconj m hb
      rw [hmU] at hb'
      exact S1248.commute_of_inverts_all hinvU ha hb'
    · set U' := U.map (MulAut.conj m).toMonoidHom
      have hS' := hconjS m hm
      have h1 : (U ⊓ U').relIndex U = 2 :=
        S1248.relIndex_inf_eq_two hS.le hS'.le hS.hyper hS'.hyper (Ne.symm hmU)
      have h2 : (U' ⊓ U).relIndex U' = 2 :=
        S1248.relIndex_inf_eq_two hS'.le hS.le hS'.hyper hS.hyper hmU
      rw [inf_comm] at h2
      have ha' := hsub U hS (U ⊓ U') inf_le_left h1 ha
      have hb' := hsub U' hS' (U ⊓ U') inf_le_right h2 (hOconj m hb)
      have hinv0 := hInv G T L V U hS z hzVL hz1 (U ⊓ U') (Or.inr ⟨inf_le_left, h1⟩)
      exact S1248.commute_of_inverts_all hinv0 ha' hb'
  by_contra hne
  set P := conjClosure O (Subgroup.normalizer (L : Set G)) with hPdef
  have hgen : ∀ a ∈ {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O, h * o * h⁻¹ = x},
      ∀ b ∈ {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O, h * o * h⁻¹ = x},
        a * b = b * a := by
    rintro _ ⟨m₁, hm₁, o₁, ho₁, rfl⟩ _ ⟨m₂, hm₂, o₂, ho₂, rfl⟩
    have hm : m₁⁻¹ * m₂ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hm₁) hm₂
    have hb : (m₁⁻¹ * m₂) * o₂ * (m₁⁻¹ * m₂)⁻¹ ∈ O.map (MulAut.conj (m₁⁻¹ * m₂)).toMonoidHom :=
      ⟨o₂, ho₂, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hc := hcommOm _ hm o₁ ho₁ _ hb
    calc m₁ * o₁ * m₁⁻¹ * (m₂ * o₂ * m₂⁻¹)
        = m₁ * (o₁ * ((m₁⁻¹ * m₂) * o₂ * (m₁⁻¹ * m₂)⁻¹)) * m₁⁻¹ := by group
      _ = m₁ * (((m₁⁻¹ * m₂) * o₂ * (m₁⁻¹ * m₂)⁻¹) * o₁) * m₁⁻¹ := by rw [hc]
      _ = m₂ * o₂ * m₂⁻¹ * (m₁ * o₁ * m₁⁻¹) := by group
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    have hS1 : Subgroup.closure {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O,
        h * o * h⁻¹ = x} ≤ Subgroup.centralizer {x | ∃ h ∈ Subgroup.normalizer (L : Set G),
          ∃ o ∈ O, h * o * h⁻¹ = x} := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro b hb
      exact hgen b hb a ha
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer (P : Set G) := by
      rw [hPdef, conjClosure, Subgroup.centralizer_closure]
      exact hS1 hb
    exact Subgroup.mem_centralizer_iff.1 hb' a ha
  have hPodd : Odd (Nat.card P) := by
    refine S1248.odd_card_of_forall_odd_pow ?_
    have hS2 : ∀ s ∈ {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O, h * o * h⁻¹ = x},
        Odd (orderOf s) := by
      rintro s ⟨h, -, o, ho, rfl⟩
      have e : h * o * h⁻¹ = (MulAut.conj h).toMonoidHom o := by simp [MulAut.conj_apply]
      rw [e, orderOf_injective _ (MulAut.conj h).injective]
      exact hoddO U o ho
    exact S1248.exists_odd_pow_eq_one_of_closure hS2 hPcomm
  have hPne : P ≠ ⊥ := fun h => hne (le_bot_iff.1 (h ▸ le_conjClosure O _))
  have hPab : IsMulCommutative ↥P :=
    ⟨⟨fun a b => Subtype.ext (hPcomm a a.2 b b.2)⟩⟩
  have hVP := hF G T L V U hS P hPne hPodd hPab (le_normalizer_conjClosure O _)
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hzx := Subgroup.mem_centralizer_iff.1 (hVP hzVL.1) x (le_conjClosure O _ hx)
  have hinv := hinvU x hx
  have hxx : x = x⁻¹ := by
    rw [← hinv, ← hzx]
    group
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hxx]
    exact mul_inv_cancel x
  have hord := orderOf_dvd_of_pow_eq_one hx2
  have hodd := hoddO U x hx
  rw [Subgroup.mem_bot]
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

end CFSG.Quasithin.H13

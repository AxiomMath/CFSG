module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AOdd3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ALift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AFin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem starOut_odd {q : TauCeti.PrimePower} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hc : Ctx B x L) (F : TD4Facts (PQuot 3 L) q) (hodd : Odd q.exponent)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hnon : ¬ InducesInnerMod 3 L b₀) :
    ∃ (bs : G) (hbs : bs ∈ cx x),
      rho L ⟨bs, hc.hXN hbs⟩ ∉ innerAutS (PQuot 3 L) ∧
      (Nat.card {y : PQuot 3 L // rho L ⟨bs, hc.hXN hbs⟩ y = y}).factorization 2 =
        6 * q.exponent ∧
      StarOut B x L (rho L ⟨bs, hc.hXN hbs⟩) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨bs, hbs, ⟨g', hg'⟩, hbs3, hψ3, hψout, hψfac, D, hD, hD9, hDfix⟩ :=
    exists_bs hc.hL hc.hXN hc.hZ F (hc.hBcx hb₀) (hc.hBel.2 b₀ hb₀) hnon
  have hbsN : bs ∈ Subgroup.normalizer (L : Set G) := hc.hXN hbs
  set ψ : MulAut (PQuot 3 L) := rho L ⟨bs, hbsN⟩ with hψ
  obtain ⟨S, hSX, hSel, hxS, ⟨n₁, hn₁, hbsS⟩, hSD, -⟩ :=
    exists_lift hc.hL hc.hXN hc.hx3 hbs hbs3 hD hDfix (M := ⊤) (fun d _ => Subgroup.mem_top _)
      (Subgroup.mem_top _)
  set N : Subgroup G := GLAPPrimeCoreOf 3 (cx x) with hN
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs => hc.hXN (hSX hs)
  have hsbX : bs * n₁ ∈ cx x := hSX hbsS
  have hsbN : bs * n₁ ∈ Subgroup.normalizer (L : Set G) := hc.hXN hsbX
  have hρsb : rho L ⟨bs * n₁, hsbN⟩ = ψ := by
    refine rho_eq_of_inv_mul_mem hc.hL hbsN hsbN ?_
    simpa using hn₁
  have hψ'out : rho L ⟨bs * n₁, hsbN⟩ ∉ innerAutS (PQuot 3 L) := by
    rw [hρsb]
    exact hψout
  have hSle : Nat.card S ≤ 81 := card_le_81 hc.hCyc hc.hZ F.toTD4Rank hSL hSel
  have hDreal : ∀ d ∈ D, ∃ s ∈ S, ∃ hs : s ∈ Subgroup.normalizer (L : Set G),
      rho L ⟨s, hs⟩ = MulAut.conj d := by
    intro d hd
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨n, hn, hlS⟩ := hSD l hd
    refine ⟨l * n, hlS, hc.hXN (hSX hlS), ?_⟩
    rw [← rho_inner L l]
    exact rho_eq_of_inv_mul_mem hc.hL (Subgroup.le_normalizer l.2) (hc.hXN (hSX hlS))
      (by simpa using hn)
  have hSge : 81 ≤ Nat.card S :=
    card_ge_81 hc.hZ hSL hSel hxS hc.hx1 hc.hx3 hc.hxker hD9 hDreal hbsS hsbN hψ'out
  have hcardS : Nat.card S = Nat.card B := by
    rw [hc.card_B F.toTD4Rank]
    omega
  obtain ⟨T₀, hT₀x, hT₀2, hBT₀, hT₀c, hT₀Q⟩ := hc.hEss
  have hT₀N : T₀ ≤ N := essential_le_core hc F hodd hT₀x hT₀2 hBT₀ hT₀c
  have hNX : N ≤ cx x := Subgroup.map_subtype_le _
  have hXN : ∀ g ∈ cx x, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 (cx x) hg) n).1 hn
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_normalizing_sylow (p := 2) (q := 3)
    S N (isPGroup_of_isElemAbelian hSel) hp3 (fun a ha h hh => hXN a (hSX ha) h hh)
    (not_dvd_card_glaPPrimeCoreOf hp3 (cx x))
  set T : Subgroup G := (P : Subgroup ↥N).map N.subtype with hT
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := P.2.map N.subtype
  obtain ⟨n, hnN, hnconj⟩ := exists_conj_into_sylow P hT₀N hT₀2
  have hBcent : (∀ s ∈ S, ∀ t ∈ T, s * t = t * s) → ∀ b ∈ B, ∀ t ∈ T₀, b * t * b⁻¹ = t := by
    intro hSc
    set Y : Subgroup G := cx x ⊓ Subgroup.centralizer (T : Set G) with hY
    have hYN : Y ≤ Subgroup.normalizer (N : Set G) := fun y hy =>
      le_normalizer_of_conj_mem hXN hy.1
    set Yh : Subgroup G := Y ⊔ N with hYh
    have hNY : N ≤ Yh := le_sup_right
    have hSY : S ≤ Y := fun s hs =>
      Subgroup.mem_inf.2 ⟨hSX hs, Subgroup.mem_centralizer_iff.2 fun t ht => (hSc s hs t ht).symm⟩
    have hSYh : S ≤ Yh := hSY.trans le_sup_left
    have hnorm := cover_normal (X := cx x) (N := N) hNX hXN P
    have hOLY : GLAPPrimeCoreOf 3 L ≤ Yh := hc.hOL.trans hNY
    have hl₀ : ∃ l₀ : ↥L, (l₀ : G) ∈ Yh ∧ (QuotientGroup.mk l₀ : PQuot 3 L) ≠ 1 := by
      have hD1 : D ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hD9
        omega
      obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
      obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective (d : PQuot 3 L)
      obtain ⟨n', hn', hlS⟩ := hSD l₀ (hl₀ ▸ d.2)
      refine ⟨l₀, ?_, fun h => hd1 (Subtype.ext (by rw [← hl₀]; exact h))⟩
      have h1 : (l₀ : G) * n' ∈ Yh := hSYh hlS
      have h2 : n' ∈ Yh := hNY hn'
      have : (l₀ : G) = ((l₀ : G) * n') * n'⁻¹ := by group
      rw [this]
      exact Yh.mul_mem h1 (Yh.inv_mem h2)
    have hLY : L ≤ Yh :=
      L_le_of_normal hc.simple (fun l hl y hy => hnorm l (hc.hLX hl) y hy) hOLY hl₀
    have hxY : x ∈ Yh := hSYh hxS
    have hbsY : bs ∈ Yh := by
      have h1 : bs * n₁ ∈ Yh := hSYh hbsS
      have : bs = (bs * n₁) * n₁⁻¹ := by group
      rw [this]
      exact Yh.mul_mem h1 (Yh.inv_mem (hNY hn₁))
    have hb₀Y : b₀ ∈ Yh := by
      have : b₀ = (g' : G)⁻¹ * bs := by rw [hg']; group
      rw [this]
      exact Yh.mul_mem (Yh.inv_mem (hLY g'.2)) hbsY
    have hBY : B ≤ Yh := hc.B_le_cover F.toTD4Rank hb₀ hnon hNY hLY hxY hb₀Y
    have hcov : ∀ b ∈ B, ∃ c ∈ Subgroup.centralizer (T₀ : Set G), ∃ u ∈ N, b = c * u := by
      intro b hb
      obtain ⟨c, hcY, u, hu, hbcu⟩ := (mem_sup_cover Y hYN).1 (hBY hb)
      have hcX : c ∈ cx x := (Subgroup.mem_inf.1 hcY).1
      have hcT : ∀ t ∈ T, t * c = c * t := fun t ht =>
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcY).2 t ht
      set c' : G := n⁻¹ * c * n with hc'
      have hc'c : c' ∈ Subgroup.centralizer (T₀ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have h1 := hcT _ (hnconj t ht)
        calc t * c' = n⁻¹ * ((n * t * n⁻¹) * c) * n := by rw [hc']; group
          _ = n⁻¹ * (c * (n * t * n⁻¹)) * n := by rw [h1]
          _ = c' * t := by rw [hc']; group
      have hc'X : c' ∈ cx x := (cx x).mul_mem ((cx x).mul_mem ((cx x).inv_mem (hNX hnN)) hcX) (hNX hnN)
      refine ⟨c', hc'c, (c'⁻¹ * c * u), ?_, by rw [← hbcu]; group⟩
      have h1 : c⁻¹ * n * c ∈ N := by
        have := hXN c⁻¹ ((cx x).inv_mem hcX) n hnN
        simpa using this
      have e : c'⁻¹ * c = n⁻¹ * (c⁻¹ * n * c) := by rw [hc']; group
      have : c'⁻¹ * c * u = (n⁻¹ * (c⁻¹ * n * c)) * u := by rw [e]
      rw [this]
      exact N.mul_mem (N.mul_mem (N.inv_mem hnN) h1) hu
    exact cover_centralizes (N := N) (T := T₀) (B := B)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp3).2
        (not_dvd_card_glaPPrimeCoreOf hp3 (cx x))))
      (isPGroup_of_isElemAbelian hc.hBel) hBT₀ hcov
  have hTc : (⁅T, S⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    have hcent : T ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hall := hBcent fun s hs t ht => Subgroup.mem_centralizer_iff.1 (hcent ht) s hs
    apply hT₀c
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := hall b hb t ht
    exact mul_inv_eq_iff_eq_mul.1 this
  have hTQ : IsEmpty (T ≃* QuaternionGroup 2) := ⟨fun eT => by
    let φ : ↥T₀ →* ↥T :=
      ((MulAut.conj n).toMonoidHom.comp T₀.subtype).codRestrict T (fun t => by
        exact hnconj t.1 t.2)
    have hφ : Function.Injective φ := fun s t hst => by
      apply Subtype.ext
      have := congrArg Subtype.val hst
      simpa [φ] using this
    have he : Function.Injective (eT.toMonoidHom.comp φ) :=
      eT.injective.comp hφ
    apply hT₀c
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := centralized_of_embed_quaternion hT₀Q (eT.toMonoidHom.comp φ) he
      (hc.hBel.2 b hb ▸ rfl : b ^ 3 = 1) (hBT₀ hb) t ht
    exact mul_inv_eq_iff_eq_mul.1 this⟩
  exact ⟨bs, hbs, hψout, hψfac, ⟨S, T, bs * n₁, hsbN, hSL, hSel, hxS, hcardS, hbsS, hρsb,
    hTN.trans hNX, hT2, hP, hTc, hTQ⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I2023

end

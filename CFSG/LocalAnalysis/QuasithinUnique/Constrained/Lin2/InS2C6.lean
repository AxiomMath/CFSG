module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2C5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

theorem card_torsion_le {A : Type*} [CommGroup A] [Finite A] {e₀ : ℕ}
    (hrank : ∀ p : ℕ, p.Prime → p ∣ e₀ → Nat.card (powMonoidHom p : A →* A).ker ≤ p ^ 2) :
    ∀ e : ℕ, 0 < e → e ∣ e₀ → Nat.card (powMonoidHom e : A →* A).ker ≤ e ^ 2 := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he hee₀
    by_cases he1 : e = 1
    · subst he1
      have : (powMonoidHom 1 : A →* A).ker = ⊥ := by
        ext x; simp
      rw [this]; simp
    · obtain ⟨p, hpp, hpe⟩ : ∃ p, p.Prime ∧ p ∣ e := ⟨e.minFac, Nat.minFac_prime he1, Nat.minFac_dvd e⟩
      obtain ⟨e', he'⟩ := hpe
      have he'pos : 0 < e' := by
        rcases Nat.eq_zero_or_pos e' with h0 | h0
        · rw [h0, mul_zero] at he'; omega
        · exact h0
      have he'lt : e' < e := by
        have := hpp.two_le
        nlinarith
      have he'd : e' ∣ e₀ := (Dvd.intro_left p he'.symm).trans hee₀
      have hpd : p ∣ e₀ := (Dvd.intro e' he'.symm).trans hee₀
      let K : Subgroup A := (powMonoidHom e : A →* A).ker
      let ψ : ↥K →* A := (powMonoidHom e' : A →* A).comp K.subtype
      have hψ : ψ.range ≤ (powMonoidHom p : A →* A).ker := by
        rintro y ⟨⟨x, hx⟩, rfl⟩
        have hx' : x ^ e = 1 := hx
        show (x ^ e') ^ p = 1
        rw [← pow_mul, mul_comm, ← he']
        exact hx'
      have hker : Nat.card ψ.ker ≤ Nat.card (powMonoidHom e' : A →* A).ker := by
        let g : ψ.ker → (powMonoidHom e' : A →* A).ker := fun z => ⟨(z.1 : A), z.2⟩
        have hg : Function.Injective g := by
          intro a b h
          have := congrArg (fun z : ↥(powMonoidHom e' : A →* A).ker => (z : A)) h
          exact Subtype.ext (Subtype.ext this)
        exact Nat.card_le_card_of_injective g hg
      have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card K := Subgroup.card_ker_mul_card_range ψ
      have h2 : Nat.card ψ.range ≤ p ^ 2 := (Subgroup.card_le_of_le hψ).trans (hrank p hpp hpd)
      calc Nat.card K = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
        _ ≤ e' ^ 2 * p ^ 2 := Nat.mul_le_mul (hker.trans (ih e' he'lt he'pos he'd)) h2
        _ = e ^ 2 := by rw [he']; ring

theorem card_le_sq_of_exp {X : Subgroup G} (hSQ : IsSQTKCat ↥X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Type*} [Group A] [Finite A] (hA : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1)
    (f : A →* G) (hf : Function.Injective f) (hX : f.range ≤ X) : Nat.card A ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p A := fun a => ⟨1, by simpa using hpow a⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have h1 : k ≤ CFSG.Open.pRank p X := le_pRank_of_injective hp.one_lt hA hpow hk f hf hX
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥X) = CFSG.Open.pRank p X :=
    pRank_top_subtype (p := p) X
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup ↥X) ≤ 2 := L238.rank_le_of_isSQTKCat hSQ hp hp2
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (by omega)

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem hall_conj_eq {B' : Subgroup G} (hH : S2Hall S L D x₀ B') {D₁ D₂ : Subgroup G}
    (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂) :
    conjR D x₀ = D := by
  have hab := B.hall_abelian hH hT₁ hT₂ hD
  let _ : CommGroup ↥B' :=
    { (inferInstance : Group ↥B') with mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have hn := B.hn
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have he₀pos : 0 < 2 ^ n - 1 := by omega
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [hm, pow_succ]
    exact ⟨2 ^ m - 1, by omega⟩
  have hX2 : pCoreOf 2 (Subgroup.normalizer (thompsonJ S : Set G)) ≠ ⊥ := by
    intro h
    have h1 : thompsonJ S ≤ pCoreOf 2 (Subgroup.normalizer (thompsonJ S : Set G)) :=
      le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl B.R_isPGroup
    rw [h] at h1
    exact C56.pCoreOf_ne_bot B.cs (le_bot_iff.1 (B.Q_le_R.trans h1))
  have hSQ : IsSQTKCat ↥(Subgroup.normalizer (thompsonJ S : Set G)) :=
    B.cs.setting.qtke.1 _ hX2
  have hrank : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
      Nat.card (powMonoidHom p : ↥B' →* ↥B').ker ≤ p ^ 2 := by
    intro p hp hpd
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hodd.not_two_dvd_nat hpd
    refine card_le_sq_of_exp hSQ hp hp2
      (A := ↥(powMonoidHom p : ↥B' →* ↥B').ker) (fun a b => ?_) (fun a => ?_)
      (B'.subtype.comp (powMonoidHom p : ↥B' →* ↥B').ker.subtype)
      ((Subgroup.subtype_injective B').comp (Subgroup.subtype_injective _)) ?_
    · exact Subtype.ext (Subtype.ext (hab a.1.1 a.1.2 b.1.1 b.1.2))
    · have h1 : (a.1 : ↥B') ^ p = 1 := a.2
      have h2 := congrArg Subtype.val h1
      exact Subtype.ext (Subtype.ext (by simpa using h2))
    · rintro y ⟨a, rfl⟩
      exact hH.le_R a.1.2
  have hTors := card_torsion_le hrank (2 ^ n - 1) he₀pos dvd_rfl
  have hN : D₂ ≤ Subgroup.normalizer (D₁ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => B.comm_elem a (hD₁L ha) b (hD₂L hb)
  have hcardD : Nat.card D = (2 ^ n - 1) ^ 2 := by
    have h := card_sup_mul_card_inf hN
    have hbot : D₂ ⊓ D₁ = ⊥ := by
      rw [eq_bot_iff, ← B.L_inf_L₂, inf_comm]
      exact inf_le_inf hD₁L hD₂L
    rw [hbot, Subgroup.card_bot, mul_one, sup_comm D₂ D₁, ← hD, hT₁.card, hT₂.card] at h
    rw [h]; ring
  have hDexp : ∀ x ∈ D, x ^ (2 ^ n - 1) = 1 := by
    intro x hx
    rw [hD] at hx
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hx
    have h1 : d₁ ^ (2 ^ n - 1) = 1 := by
      have := orderOf_dvd_natCard (⟨d₁, hd₁⟩ : D₁)
      rw [Subgroup.orderOf_mk, hT₁.card] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have h2 : d₂ ^ (2 ^ n - 1) = 1 := by
      have := orderOf_dvd_natCard (⟨d₂, hd₂⟩ : D₂)
      rw [Subgroup.orderOf_mk, hT₂.card] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hc : Commute d₁ d₂ := B.comm_elem d₁ (hD₁L hd₁) d₂ (hD₂L hd₂)
    rw [hc.mul_pow, h1, h2, one_mul]
  have hDyexp : ∀ x ∈ conjR D x₀, x ^ (2 ^ n - 1) = 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hx
    have := conj_pow (a := x₀⁻¹) (b := d) (i := 2 ^ n - 1)
    rw [inv_inv] at this
    rw [this, hDexp d hd]
    group
  have hDyle : conjR D x₀ ≤ B' := hH.eq_sup ▸ le_sup_right
  have hD₁eq : D.subgroupOf B' = (powMonoidHom (2 ^ n - 1) : ↥B' →* ↥B').ker := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · exact Subtype.ext (hDexp x hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH.D_le).toEquiv, hcardD]
      exact hTors
  have hD₂eq : (conjR D x₀).subgroupOf B' = (powMonoidHom (2 ^ n - 1) : ↥B' →* ↥B').ker := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · exact Subtype.ext (hDyexp x hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDyle).toEquiv, card_conjR, hcardD]
      exact hTors
  have := Subgroup.subgroupOf_inj.1 (hD₂eq.trans hD₁eq.symm)
  rwa [inf_eq_left.2 hDyle, inf_eq_left.2 hH.D_le] at this

end S2Base

end CFSG.QuasithinUnique.Lin2

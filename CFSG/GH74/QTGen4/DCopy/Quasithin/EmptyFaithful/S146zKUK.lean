module

public import CFSG.Quasithin.EmptyFaithful.S146zKUK
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section UKz

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.commutator_uK_ne_bot_F4 (S : Setting146 G T M) (h5 : Stage1461Five)
    (h16 : Stage14616_F4) (h4 : Stage1463Four) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {g : G}
    (hnc : ¬ ⁅uHi T M H H₁, conjSub g⁻¹ (conjClosure (VZ T M) H)⁆ ≤ quasithinOmegaOneCenter T)
    (hn : conjSub g⁻¹ (conjClosure (VZ T M) H) ≤
      H ⊓ Subgroup.normalizer (uHi T M H H₁ : Set G))
    (hle : conjClosure (VZ T M) H ≤ conjSub g⁻¹ H) :
    ⁅uK T M H, conjSub g⁻¹ (uK T M H)⁆ ≠ ⊥ := by
  classical
  intro hbad
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHC : ∀ y ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y := by
    intro y hy z hz
    have h1 := hHN hy
    rw [normalizer_eq_centralizer_of_card_eq_two S.card_Z] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hUH : conjClosure (VZ T M) H ≤ H :=
    (S.conjClosure_le_pCoreOf hH).trans (pCoreOf_le 2 H)
  have hUZ : ∀ y ∈ conjClosure (VZ T M) H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y :=
    fun y hy z hz => hHC y (hUH hy) z hz
  have hKU : uK T M H ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _)

  have hZK : quasithinOmegaOneCenter T ≤ uK T M H := by
    have h1 := (Z_le_commutator_of_isDecP h5 S hred (h.toIsDecP hred)).1
    exact h1.trans (Subgroup.commutator_mono le_rfl
      (((oTwoUpper_le H₁).trans h.le₁).trans h.le))
  have huHi_le : ∀ Hi : Subgroup G, Hi ≤ H → uHi T M H Hi ≤ uK T M H := fun Hi hHi => by
    unfold uHi
    exact sup_le (Subgroup.commutator_mono le_rfl hHi) hZK

  obtain ⟨u₁, hu₁, -, u₂, hu₂, -, c, hcU, hcH, hV⟩ :=
    input14617V_proved G T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t h
  have hu₁K : u₁ ∈ uK T M H := huHi_le H₁ hH₁H hu₁
  have hu₂K : u₂ ∈ uK T M H := huHi_le H₂ (h.le₂.trans h.le) hu₂
  have hUsup : conjClosure (VZ T M) H ≤ uK T M H ⊔ Subgroup.zpowers c := by
    rw [conjClosure_eq_sup_uK_z T M H]
    refine sup_le ?_ le_sup_left
    rw [hV]
    refine sup_le (hZK.trans le_sup_left) (Subgroup.zpowers_le.mpr ?_)
    exact (uK T M H ⊔ Subgroup.zpowers c).mul_mem
      ((uK T M H ⊔ Subgroup.zpowers c).mul_mem (Subgroup.mem_sup_left hu₁K)
        (Subgroup.mem_sup_left hu₂K)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ uHi T M H H₁, ∃ b ∈ conjSub g⁻¹ (conjClosure (VZ T M) H),
      a * b * a⁻¹ * b⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    apply hnc
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact hall a ha b hb
  have haU : a ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H ha
  have haK : a ∈ uK T M H := huHi_le H₁ hH₁H ha
  have hbU : g * b * g⁻¹ ∈ conjClosure (VZ T M) H := by
    have := mem_conjSub.mp hb
    simpa using this
  have hκH : g * a * g⁻¹ ∈ H := by
    have := mem_conjSub.mp (hle haU)
    simpa using this

  have hK : ∀ y ∈ uK T M H, (g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹ * y⁻¹ ∈
      quasithinOmegaOneCenter T := by
    intro y hy
    have hyg : g⁻¹ * y * g ∈ conjSub g⁻¹ (uK T M H) := by
      rw [mem_conjSub]
      have e : (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 : ⁅a, g⁻¹ * y * g⁆ ∈ ⁅uK T M H, conjSub g⁻¹ (uK T M H)⁆ :=
      Subgroup.commutator_mem_commutator haK hyg
    rw [hbad, Subgroup.mem_bot, commutatorElement_def] at h1
    have e : (g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹ * y⁻¹ =
        g * (a * (g⁻¹ * y * g) * a⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e, h1, mul_one, mul_inv_cancel]
    exact (quasithinOmegaOneCenter T).one_mem
  have hcZ : (g * a * g⁻¹) * c * (g * a * g⁻¹)⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T :=
    hcH _ hκH
  have hall := forall_commutator_mem_of_gens hUZ hKU hcU hUsup hK hcZ
  have hz := hall _ hbU
  obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : G, u₀ = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hu₀def] at hab
  have hz' : g * u₀ * g⁻¹ ∈ quasithinOmegaOneCenter T := by
    have e : g * u₀ * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by
      rw [hu₀def]
      group
    rw [e]
    exact hz
  have hu₀H : u₀ ∈ uHi T M H H₁ := by
    have hbN := (hn hb).2
    have h1 := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp ((uHi T M H H₁).inv_mem ha)
    have e : u₀ = a * (b * a⁻¹ * b⁻¹) := by
      rw [hu₀def]
      group
    rw [e]
    exact (uHi T M H H₁).mul_mem ha h1
  have hz1 : g * u₀ * g⁻¹ ≠ 1 := by
    intro h1
    apply hab
    have : u₀ = 1 := by
      have h2 := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using h2
    rw [this]
    exact (quasithinOmegaOneCenter T).one_mem
  obtain ⟨y₀, hy₀, hyT⟩ :=
    input14617Orbit_proved G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t h u₀ hu₀H hab
  exact h.false_of_conj_gen_F4 S h5 h16 h4 hred hmax hMod hF hu₀H hab hz' hz1
    (g := g⁻¹) (z := g * u₀ * g⁻¹) (y := y₀) (by group) (h.le₁ hy₀) hyT

end UKz

theorem input14617UK_of_stages_F4 (h5 : Stage1461Five) (h14 : Stage14614_F4) (h16 : Stage14616_F4)
    (h4 : Stage1463Four) (iMod : Input14617Mod) (iF : Input14617Fstar) : Input14617UK_F4 := by
  intro G _ _ T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec hcase u hu huZ _ hInv
  have hH : IsHTM T M H := hred.isHTM
  have hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T) :=
    iF G T M S H PQ p hred hmax (stage14614At_of_F4 h14 S hred hmax)
  have h1 : (tU T u).relIndex (tZero T u) = 2 := (stage1463_one_proof G T M S H hH u hInv).2.1
  have core : ∀ (H₁' H₂' : Subgroup G) (t' : G) (hdec' : IsDec12 T M H p H₀ H₁' H₂' t'),
      (u ∈ uHi T M H H₁' ∨ u ∈ uHi T M H H₂') → Case13One T M H p H₁' →
        ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
          ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥ := by
    intro H₁' H₂' t' hdec' hu' hc
    obtain ⟨-, -, g, -, hnc, hn, hle⟩ := hc
    have hKbad := hdec'.commutator_uK_ne_bot_F4 S h5 h16 h4 hred hmax hp3 hOF
      (iMod G T M S H PQ p hred H₀ H₁' H₂' t' hdec') hF hnc hn hle
    exact hdec'.exists_conj_uK S hred hp3 hOF hnc hn hle hKbad hu' huZ h1
  rcases hcase with hc | hc
  · exact core H₁ H₂ t hdec hu hc
  · exact core H₂ H₁ t⁻¹ hdec.swap hu.symm hc

end CFSG.Quasithin

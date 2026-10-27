module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RGen
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

variable {G : Type} [Group G]

theorem mul_self_of_orderOf_two {g : G} (h : orderOf g = 2) : g * g = 1 := by
  have := pow_orderOf_eq_one g
  rwa [h, sq] at this

theorem mem_map_conj_iff {P₀ : Subgroup G} {g w : G} :
    w ∈ P₀.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ P₀ := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hp
  · intro h
    exact ⟨g⁻¹ * w * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem isDihedralMaxIn_map_conj {P₀ P : Subgroup G} {g : G} (h : IsDihedralMaxIn P₀ P)
    (hg : ∀ w ∈ P, g * w * g⁻¹ ∈ P) :
    IsDihedralMaxIn (P₀.map (MulAut.conj g).toMonoidHom) P := by
  have hcard : Nat.card ↥(P₀.map (MulAut.conj g).toMonoidHom) = Nat.card ↥P₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨?_, by rw [hcard]; exact h.2.1, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hg p (h.1 hp)
  · rw [hcard]
    exact SP.Local.CtW.isDihedralOrder_of_mulEquiv
      (Subgroup.equivMapOfInjective P₀ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) h.2.2

variable [Finite G]

omit [Finite G] in
theorem conj_P_and_z {K T : Subgroup G} {z : G}
    (hPgen : T ⊓ K = closure {u : G | u ∈ thompsonJ2 T ∧ IsConj z u})
    (hz1 : z ≠ 1) (hzP : z ∈ T ⊓ K) (hzc : ∀ t ∈ T, t * z = z * t)
    (hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z)
    {g : G} (hg : g ∈ normalizer (T : Set G)) :
    (∀ w ∈ T ⊓ K, g * w * g⁻¹ ∈ T ⊓ K) ∧ g * z * g⁻¹ = z := by
  have hconj : ∀ {g : G}, g ∈ normalizer (T : Set G) → ∀ w ∈ T ⊓ K, g * w * g⁻¹ ∈ T ⊓ K := by
    intro g hg w hw
    rw [hPgen] at hw ⊢
    refine conj_mem_closure (S := {u : G | u ∈ thompsonJ2 T ∧ IsConj z u}) (fun u hu => ?_) hw
    refine ⟨conj_mem_thompsonJ2 hg hu.1, ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hu.2
    exact isConj_iff.2 ⟨g * c, by rw [← hc]; group⟩
  have hg' : g⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hg
  refine ⟨hconj hg, ?_⟩
  have hgz : g * z * g⁻¹ ∈ T ⊓ K := hconj hg z hzP
  have hcomm : ∀ p ∈ T ⊓ K, (g * z * g⁻¹) * p = p * (g * z * g⁻¹) := by
    intro p hp
    have hp' : g⁻¹ * p * g ∈ T ⊓ K := by
      have := hconj hg' p hp
      simpa using this
    have hc := hzc _ hp'.1
    calc (g * z * g⁻¹) * p = g * (z * (g⁻¹ * p * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * p * g) * z) * g⁻¹ := by rw [hc]
      _ = p * (g * z * g⁻¹) := by group
  rcases hzu _ hgz hcomm with h | h
  · exfalso
    apply hz1
    have h1 : g * z * g⁻¹ = 1 := h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · exact h


theorem exists_frame
    {x y : G} {K T V W : Subgroup G} {f z : G}
    (cfg : Cfg3 x y K T V W f z)
    (hnc : ¬ CFSG.GH74.IsCentralInvolution x)
    (hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(T ⊓ K) n)
    (hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z)
    (h37b : (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) = ⊥)
    (h37c : zCenter (thompsonJ2 T) = zpowers z ⊔ zpowers f ⊔ zpowers x)
    (h37d : ∀ P₀ : Subgroup G, IsDihedralMaxIn P₀ (T ⊓ K) →
      T ⊓ centralizer ({f} : Set G) = T ⊓ normalizer (P₀ : Set G))
    (h38 : ∀ (S : Subgroup G) (a : G), IsSylowOf 2 S ⊤ → T ≤ S → a ∈ S →
      a ∈ normalizer (T : Set G) → a ∉ T → a ^ 2 ∈ T →
      (zCenter T = zpowers x ⊔ zpowers z ∧
        Nat.card ↥T = 2 * Nat.card ↥(T ⊓ centralizer ((zCenter (thompsonJ2 T) : Subgroup G) : Set G))) ∧
      (T ⊓ K = closure {u : G | u ∈ thompsonJ2 T ∧ IsConj z u} ∧
        ∀ P₀ : Subgroup G, IsDihedralMaxIn P₀ (T ⊓ K) → ¬ ∀ t ∈ T, ∀ p ∈ P₀, t * p * t⁻¹ ∈ P₀) ∧
      (S ⊓ normalizer (T : Set G) = T ⊔ zpowers a ∧ a * x * a⁻¹ = x * z)) :
    ∃ (S : Subgroup G) (a : G) (P₀ : Subgroup G) (f₁ : G),
      IsSylowOf 2 S ⊤ ∧ T ≤ S ∧ T ≠ S ∧ a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T ∧
      IsDihedralMaxIn P₀ (T ⊓ K) ∧ a ∈ normalizer (P₀ : Set G) ∧
      a * x * a⁻¹ = x * z ∧ a * z * a⁻¹ = z ∧ (f₁ = f ∨ f₁ = f * x) ∧ a * f₁ * a⁻¹ = f₁ := by
  have hx2 : orderOf x = 2 := cfg.hx2
  have hxx : x * x = 1 := mul_self_of_orderOf_two hx2
  have hff : f * f = 1 := mul_self_of_orderOf_two cfg.hf2
  obtain ⟨hzP, hz2, hzc⟩ := cfg.z_mem
  have hzz : z * z = 1 := mul_self_of_orderOf_two hz2
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hxT : x ∈ T := cfg.x_mem_T
  have hTle : T ≤ centralizer ({x} : Set G) := cfg.setup.sylowT.le
  have hxc : ∀ t ∈ T, t * x = x * t := fun t ht => mem_centralizer_singleton_iff.1 (hTle ht)
  have hTp : IsPGroup 2 ↥T := cfg.setup.sylowT.isPGroup
  obtain ⟨S, hS, hTS, hTne⟩ := exists_sylow_ne hTp hx2 hxT hxc hnc
  obtain ⟨a₀, ha₀S, ha₀N, ha₀T, ha₀2⟩ := exists_a₀ hS.isPGroup hTS hTne
  obtain ⟨-, ⟨hPgen, hP0nn⟩, -, -⟩ := h38 S a₀ hS hTS ha₀S ha₀N ha₀T ha₀2
  obtain ⟨n, hn3, hdn⟩ := hdih
  obtain ⟨P₀, hP₀⟩ := exists_isDihedralMaxIn hn3 hdn
  have hP₀nn := hP0nn P₀ hP₀
  push Not at hP₀nn
  obtain ⟨t, htT, p, hpP₀, hptP₀⟩ := hP₀nn
  have htN : t ∈ normalizer (T : Set G) := Subgroup.le_normalizer htT
  have htS : t ∈ S := hTS htT
  have hPc₀ := (conj_P_and_z hPgen hz1 hzP hzc hzu ha₀N).1
  have hPct := (conj_P_and_z hPgen hz1 hzP hzc hzu htN).1
  have hB := isDihedralMaxIn_map_conj hP₀ hPc₀
  have hC := isDihedralMaxIn_map_conj hP₀ hPct
  have hAC : P₀ ≠ P₀.map (MulAut.conj t).toMonoidHom := by
    intro h
    apply hptP₀
    rw [h]
    exact ⟨p, hpP₀, by simp [MulAut.conj_apply]⟩
  obtain ⟨a, haS, haN, haT, ha2, haP₀⟩ : ∃ a : G, a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧
      a ^ 2 ∈ T ∧ a ∈ normalizer (P₀ : Set G) := by
    rcases eq_of_isDihedralMaxIn_three hn3 hdn hP₀ hB hC with h | h | h
    · refine ⟨a₀, ha₀S, ha₀N, ha₀T, ha₀2, ?_⟩
      have h' : ∀ w, w ∈ P₀ ↔ a₀⁻¹ * w * a₀ ∈ P₀ := fun w => by
        rw [← mem_map_conj_iff, ← h]
      have : a₀⁻¹ ∈ normalizer (P₀ : Set G) := by
        refine Subgroup.mem_normalizer_iff.2 fun w => ?_
        simpa using h' w
      simpa using (normalizer (P₀ : Set G)).inv_mem this
    · refine ⟨t⁻¹ * a₀, S.mul_mem (S.inv_mem htS) ha₀S,
        (normalizer (T : Set G)).mul_mem ((normalizer (T : Set G)).inv_mem htN) ha₀N, ?_, ?_, ?_⟩
      · intro h1
        apply ha₀T
        have := T.mul_mem htT h1
        simpa using this
      · have h1 : a₀ * t⁻¹ * a₀⁻¹ ∈ T := by
          have := (Subgroup.mem_normalizer_iff.1 ha₀N t⁻¹).1 (T.inv_mem htT)
          exact this
        have h2 : (t⁻¹ * a₀) ^ 2 = t⁻¹ * (a₀ * t⁻¹ * a₀⁻¹) * a₀ ^ 2 := by simp only [sq]; group
        rw [h2]
        exact T.mul_mem (T.mul_mem (T.inv_mem htT) h1) ha₀2
      · refine Thm1L3.mem_normalizer_of_conj_le fun w hw => ?_
        have hw' : a₀ * w * a₀⁻¹ ∈ P₀.map (MulAut.conj a₀).toMonoidHom :=
          ⟨w, hw, by simp [MulAut.conj_apply]⟩
        rw [h] at hw'
        have := mem_map_conj_iff.1 hw'
        simpa [mul_assoc] using this
    · exact absurd h hAC
  obtain ⟨-, -, -, hax⟩ := h38 S a hS hTS haS haN haT ha2
  obtain ⟨-, haz⟩ := conj_P_and_z (h38 S a hS hTS haS haN haT ha2).2.1.1 hz1 hzP hzc hzu haN
  refine ⟨S, a, P₀, ?_⟩
  have hzf : z * f = f * z := (cfg.mem.2.2.1 z hzP).symm
  have hzx : z * x = x * z := (hzc x hxT).symm
  have hfx : f * x = x * f := cfg.hxf.symm
  have hf1 : f ≠ 1 := fun h => by
    have := cfg.hf2
    rw [h, orderOf_one] at this
    omega
  have hfx' : f ≠ x := cfg.mem.2.2.2.1
  have hzmem : ∀ {g : G}, g ∈ zpowers f ⊔ zpowers x → g ∈ T ⊓ K → g = 1 := by
    intro g hg hgP
    have : g ∈ (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) := ⟨hgP, hg⟩
    rw [h37b] at this
    exact Subgroup.mem_bot.1 this
  have hfz : f ≠ z := fun h => hz1 (hzmem (by rw [← h]; exact mem_sup_left (mem_zpowers f)) hzP)
  have hfzx : f ≠ z * x := by
    intro h
    apply hz1
    refine hzmem ?_ hzP
    have hz' : z = f * x := by rw [h]; calc z = z * (x * x) := by rw [hxx, mul_one]
      _ = z * x * x := by rw [mul_assoc]
    rw [hz']
    exact (zpowers f ⊔ zpowers x).mul_mem (mem_sup_left (mem_zpowers f)) (mem_sup_right (mem_zpowers x))
  have hfA : f ∈ zCenter (thompsonJ2 T) := by
    rw [h37c]; exact mem_sup_left (mem_sup_right (mem_zpowers f))
  have haJ : a ∈ normalizer ((thompsonJ2 T : Subgroup G) : Set G) :=
    Thm1L3.mem_normalizer_of_conj_le fun j hj => conj_mem_thompsonJ2 haN hj
  have haA : a * f * a⁻¹ ∈ zpowers z ⊔ zpowers f ⊔ zpowers x := by
    have := conj_mem_zCenter haJ hfA
    rwa [h37c] at this
  have ha2f : a * (a * f * a⁻¹) * a⁻¹ = f := by
    have h1 : a ^ 2 ∈ T ⊓ normalizer (P₀ : Set G) := ⟨ha2, (normalizer (P₀ : Set G)).pow_mem haP₀ 2⟩
    rw [← h37d P₀ hP₀] at h1
    have h2 : a ^ 2 * f = f * a ^ 2 := mem_centralizer_singleton_iff.1 h1.2
    calc a * (a * f * a⁻¹) * a⁻¹ = a ^ 2 * f * (a ^ 2)⁻¹ := by simp only [sq]; group
      _ = f * a ^ 2 * (a ^ 2)⁻¹ := by rw [h2]
      _ = f := by simp only [sq]; group
  obtain ⟨f₁, hf₁, haf₁⟩ := exists_fixed_f₁ hzz hff hxx hzf hzx hfx hz1 hf1 hfz hfx' hfzx haA hax haz ha2f
  exact ⟨f₁, hS, hTS, hTne, haS, haN, haT, ha2, hP₀, haP₀, hax, haz, hf₁, haf₁⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R

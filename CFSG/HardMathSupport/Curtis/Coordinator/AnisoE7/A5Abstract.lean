module

public import CFSG.HardMathSupport.Lang.TwE6Step3.FixedSplit
public import CFSG.HardMathSupport.Lang.TwE6Step3.Glue
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Decomp
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5LayerBeta

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.LieType.SeitzGeneration CFSG.Open CFSG.HardMathSupport.Lang.TwE6Step3

section Extend

variable {M C : Type*} [Group M] [Group C]

theorem exists_hom_sup_of_centralizing {Z P : Subgroup M}
    (hZP : ∀ z ∈ Z, ∀ u ∈ P, z * u = u * z) (ρ : P →* C)
    (hρ : ∀ (w : M) (hwP : w ∈ P), w ∈ Z → ρ ⟨w, hwP⟩ = 1) :
    ∃ ρ' : (Z ⊔ P : Subgroup M) →* C,
      (∀ (u : M) (hu : u ∈ P), ρ' ⟨u, Subgroup.mem_sup_right hu⟩ = ρ ⟨u, hu⟩) ∧
      ∀ (z : M) (hz : z ∈ Z), ρ' ⟨z, Subgroup.mem_sup_left hz⟩ = 1 := by
  classical
  have hn : Z ≤ Subgroup.normalizer (P : Set M) := le_normalizer_of_commute hZP
  have hmem : ∀ x : (Z ⊔ P : Subgroup M), ∃ z ∈ Z, ∃ u ∈ P, (x : M) = z * u := by
    intro x
    have hx : (x : M) ∈ ((Z ⊔ P : Subgroup M) : Set M) := x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Z P hn] at hx
    obtain ⟨z, hz, u, hu, h⟩ := hx
    exact ⟨z, hz, u, hu, h.symm⟩
  have huniq : ∀ (z z' u u' : M) (hz : z ∈ Z) (hz' : z' ∈ Z) (hu : u ∈ P) (hu' : u' ∈ P),
      z * u = z' * u' → ρ ⟨u, hu⟩ = ρ ⟨u', hu'⟩ := by
    intro z z' u u' hz hz' hu hu' h
    have h1 : u * u'⁻¹ = z⁻¹ * z' := by
      calc u * u'⁻¹ = z⁻¹ * (z * u) * u'⁻¹ := by group
        _ = z⁻¹ * (z' * u') * u'⁻¹ := by rw [h]
        _ = z⁻¹ * z' := by group
    have hP : u * u'⁻¹ ∈ P := P.mul_mem hu (P.inv_mem hu')
    have hZ' : u * u'⁻¹ ∈ Z := by rw [h1]; exact Z.mul_mem (Z.inv_mem hz) hz'
    have := hρ _ hP hZ'
    have h2 : ρ ⟨u * u'⁻¹, hP⟩ = ρ ⟨u, hu⟩ * (ρ ⟨u', hu'⟩)⁻¹ := by
      rw [show (⟨u * u'⁻¹, hP⟩ : P) = ⟨u, hu⟩ * ⟨u', hu'⟩⁻¹ from rfl, map_mul, map_inv]
    rw [h2, mul_inv_eq_one] at this
    exact this
  let f : (Z ⊔ P : Subgroup M) → C := fun x =>
    ρ ⟨(hmem x).choose_spec.2.choose, (hmem x).choose_spec.2.choose_spec.1⟩
  have hf : ∀ (x : (Z ⊔ P : Subgroup M)) (z u : M) (hz : z ∈ Z) (hu : u ∈ P), (x : M) = z * u →
      f x = ρ ⟨u, hu⟩ := by
    intro x z u hz hu h
    obtain ⟨hz0, -⟩ := (hmem x).choose_spec
    have hspec := (hmem x).choose_spec.2.choose_spec.2
    exact huniq _ _ _ _ (hmem x).choose_spec.1 hz _ hu (hspec.symm.trans h)
  refine ⟨
    { toFun := f
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_⟩
  · have := hf 1 1 1 Z.one_mem P.one_mem (by simp)
    exact this.trans (map_one ρ)
  · intro x y
    obtain ⟨z, hz, u, hu, hx⟩ := hmem x
    obtain ⟨z', hz', u', hu', hy⟩ := hmem y
    have hxy : ((x * y : (Z ⊔ P : Subgroup M)) : M) = (z * z') * (u * u') := by
      show (x : M) * (y : M) = _
      rw [hx, hy]
      have := hZP z' hz' u hu
      calc z * u * (z' * u') = z * (u * z') * u' := by group
        _ = z * (z' * u) * u' := by rw [this]
        _ = _ := by group
    rw [hf (x * y) (z * z') (u * u') (Z.mul_mem hz hz') (P.mul_mem hu hu') hxy,
      hf x z u hz hu hx, hf y z' u' hz' hu' hy]
    exact (map_mul ρ ⟨u, hu⟩ ⟨u', hu'⟩)
  · intro u hu
    exact hf _ 1 u Z.one_mem hu (by simp)
  · intro z hz
    have := hf ⟨z, Subgroup.mem_sup_left hz⟩ z 1 hz P.one_mem (by simp)
    exact this.trans (map_one ρ)

end Extend

section Split

variable {M : Type*} [Group M]

theorem exists_split_of_fixed (θ : M →* M) {H Q P : Subgroup M}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHQ : H ≤ Subgroup.normalizer (Q : Set M))
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ : ∀ g ∈ Q, θ g ∈ Q)
    (hlang : ∀ s ∈ H ⊓ Q, ∃ t ∈ H ⊓ Q, t⁻¹ * θ t = s)
    (hΓ : ∀ g ∈ Q, θ g = g → ∃ s ∈ H ⊓ Q, θ s = s ∧ ∃ x ∈ P, g = s * x)
    {m : M} (hm : m ∈ H ⊔ Q) (hθm : θ m = m) :
    ∃ a ∈ H, θ a = a ∧ ∃ x ∈ P, m = a * x := by
  obtain ⟨t, htH, hθt, g, hgQ, hθg, rfl⟩ := exists_fixed_split θ hH hHQ hθH hθQ hlang hm hθm
  obtain ⟨s, hsHQ, hθs, x, hxP, rfl⟩ := hΓ g hgQ hθg
  refine ⟨t * s, H.mul_mem htH (Subgroup.mem_inf.1 hsHQ).1, ?_, x, hxP, by group⟩
  rw [map_mul, hθt, hθs]

end Split

section Compat

variable {M C : Type*} [Group M] [Group C]

theorem commute_of_decomp {P Z : Subgroup M} {p : ℕ} (hpp : p.Prime) (hp3 : 3 < p)
    (ρ : P →* C) (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z)
    (hkcard : Nat.card ρ.ker ∣ 6)
    (hZP : ∀ z ∈ Z, ∀ u ∈ P, z * u = u * z)
    (hZker : ∀ (w : M) (hw : w ∈ P), w ∈ Z → ρ ⟨w, hw⟩ = 1)
    {m z x w : M} (hmz : m = z * x) (hz : z ∈ Z) (hx : x ∈ P) (hw : w ∈ P) (hmp : m ^ p = 1)
    (h : ρ ⟨x, hx⟩ * ρ ⟨w, hw⟩ = ρ ⟨w, hw⟩ * ρ ⟨x, hx⟩) : m * w = w * m := by
  have hcop6 : Nat.Coprime 6 p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 ?_)
    intro hd
    have : p ∣ 2 * 3 := hd
    rcases (Nat.Prime.dvd_mul hpp).1 this with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have hkp : Nat.Coprime (Nat.card ρ.ker) p := Nat.Coprime.coprime_dvd_left hkcard hcop6
  have hzx : z * x = x * z := hZP z hz x hx
  have hxp : x ^ p = (z ^ p)⁻¹ := by
    have : z ^ p * x ^ p = 1 := by rw [← (Commute.mul_pow hzx p), ← hmz, hmp]
    exact eq_inv_of_mul_eq_one_right this
  have hxpP : x ^ p ∈ P := P.pow_mem hx p
  have hxpZ : x ^ p ∈ Z := by rw [hxp]; exact Z.inv_mem (Z.pow_mem hz p)
  have hkerxp : (⟨x ^ p, hxpP⟩ : P) ∈ ρ.ker := hZker _ hxpP hxpZ
  have hker6 : ∀ v : ρ.ker, v ^ 6 = 1 := fun v =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard v).trans hkcard)
  have hxp6 : ((x ^ p) ^ 6 : M) = 1 := by
    have := hker6 ⟨⟨x ^ p, hxpP⟩, hkerxp⟩
    exact congrArg (fun v : ρ.ker => ((v : P) : M)) this
  obtain ⟨c', d', hcd⟩ := (Nat.isCoprime_iff_coprime.2 hcop6 : IsCoprime ((6 : ℕ) : ℤ) (p : ℤ))
  have hcd' : c' * 6 + d' * p = 1 := by simpa using hcd
  set x' : M := (x ^ 6) ^ c' with hx'
  have hx'P : x' ∈ P := P.zpow_mem (P.pow_mem hx 6) c'
  have hx6p : (x ^ 6) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxp6]
  have hx'p : x' ^ p = 1 := by
    have e : ((x ^ 6) ^ c') ^ p = ((x ^ 6) ^ p) ^ c' := by
      rw [← zpow_natCast ((x ^ 6) ^ c') p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [hx', e, hx6p, one_zpow]
  have hxdec : x = x' * (x ^ p) ^ d' := by
    have e1 : x = x ^ (c' * 6 + d' * p) := by rw [hcd', zpow_one]
    calc x = x ^ (c' * 6 + d' * (p : ℤ)) := e1
      _ = x' * (x ^ p) ^ d' := by
        rw [zpow_add, hx', ← zpow_natCast x 6, ← zpow_mul, ← zpow_natCast x p, ← zpow_mul]
        norm_cast
        simp [mul_comm]
  set c : M := (x ^ p) ^ d' with hc
  have hcP : c ∈ P := P.zpow_mem hxpP d'
  have hcker : (⟨c, hcP⟩ : P) ∈ ρ.ker := by
    have : (⟨c, hcP⟩ : P) = (⟨x ^ p, hxpP⟩ : P) ^ d' := rfl
    rw [this]
    exact ρ.ker.zpow_mem hkerxp d'
  have hρx : ρ ⟨x, hx⟩ = ρ ⟨x', hx'P⟩ := by
    have : (⟨x, hx⟩ : P) = ⟨x', hx'P⟩ * ⟨c, hcP⟩ := Subtype.ext hxdec
    rw [this, map_mul, MonoidHom.mem_ker.1 hcker, mul_one]
  have hcw : c * w = w * c := congrArg Subtype.val (hkc _ hcker ⟨w, hw⟩)
  have hx'w : x' * w = w * x' := by
    have h' : ρ ⟨x', hx'P⟩ * ρ ⟨w, hw⟩ = ρ ⟨w, hw⟩ * ρ ⟨x', hx'P⟩ := by rw [← hρx]; exact h
    have := commute_of_commute_map ρ hkc hkp (x := ⟨x', hx'P⟩) (l := ⟨w, hw⟩)
      (Subtype.ext hx'p) h'
    exact congrArg Subtype.val this
  have hxw : x * w = w * x := by
    rw [hxdec, mul_assoc, hcw, ← mul_assoc, hx'w, mul_assoc]
  rw [hmz, mul_assoc, hxw, ← mul_assoc, hZP z hz w hw, mul_assoc]

end Compat

section Main

theorem centralizer_le_hyperClosure_of_abstract_a5
    {G M : Type*} [Group G] [Group M] (θ : M →* M) {H Q P : Subgroup M} {p : ℕ}
    (hpp : p.Prime) (hp3 : 3 < p)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid)
    (hpq : p ∣ q.card ^ 2 - q.card + 1)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHQ : H ≤ Subgroup.normalizer (Q : Set M))
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ : ∀ g ∈ Q, θ g ∈ Q)
    (hθZ : ∀ z ∈ H, (∀ q ∈ Q, z * q = q * z) → ∀ q ∈ Q, θ z * q = q * θ z)
    (hlang : ∀ s ∈ H ⊓ Q, ∃ t ∈ H ⊓ Q, t⁻¹ * θ t = s)
    (hΓ : ∀ g ∈ Q, θ g = g → ∃ s ∈ H ⊓ Q, θ s = s ∧ ∃ x ∈ P, g = s * x)
    (hPQ : P ≤ Q) (hPfix : ∀ x ∈ P, θ x = x)
    (hfree : ∀ m ∈ H ⊔ Q, (∀ u ∈ P, m * u = u * m) → m ∈ H ∧ ∀ g ∈ Q, m * g = g * m)
    (h4 : ∀ t ∈ H, θ t = t → ∃ z ∈ H, (∀ q ∈ Q, z * q = q * z) ∧ ∃ s ∈ H ⊓ Q, t ^ 6 = z * s)
    (h5 : ∀ f ∈ H ⊓ Q, (∀ q ∈ Q, f * q = q * f) → f ^ 6 = 1)
    (h6 : ∀ g ∈ Q, θ g = g → g ^ 6 ∈ P)
    (ρ : P →* Cat ⟨.twistedA 5 q, hv⟩) (hρ : Function.Surjective ρ)
    (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z) (hkcard : Nat.card ρ.ker ∣ 6)
    (ψ : G →* M) (hψ : Function.Injective ψ) (E : Subgroup G) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hψE : ∀ e ∈ E, ψ e ∈ H ∧ θ (ψ e) = ψ e)
    {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hψy : ∀ g ∈ Q, ψ y * g = g * ψ y)
    (hψN : ∀ k : G, k * y = y * k → ψ k ∈ H ⊔ Q ∧ θ (ψ k) = ψ k)
    (hPψ : ∀ u ∈ P, ∃ g : G, ψ g = u) :
    Subgroup.centralizer ({y} : Set G) ≤ hyperClosure p (⊤ : Subgroup G) E := by
  classical
  have : Fact p.Prime := ⟨hpp⟩
  have hp3' : p ≠ 3 := by omega
  set Z₀ : Subgroup M := H ⊓ MonoidHom.eqLocus θ (MonoidHom.id M) ⊓
    Subgroup.centralizer (Q : Set M) with hZ₀
  have hmemZ₀ : ∀ z, z ∈ Z₀ ↔ z ∈ H ∧ θ z = z ∧ ∀ g ∈ Q, z * g = g * z := by
    intro z
    simp only [hZ₀, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    change (z ∈ H ∧ θ z = z) ∧ _ ↔ _
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun g hg => (h3 g hg).symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun g hg => (h3 g hg).symm⟩
  have hZP : ∀ z ∈ Z₀, ∀ u ∈ P, z * u = u * z := fun z hz u hu =>
    ((hmemZ₀ z).1 hz).2.2 u (hPQ hu)
  have hcenter := catTwistedAFive_center_eq_bot hv
  have hZker : ∀ (w : M) (hw : w ∈ P), w ∈ Z₀ → ρ ⟨w, hw⟩ = 1 := by
    intro w hw hwZ
    have : ρ ⟨w, hw⟩ ∈ Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩) := by
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨u, rfl⟩ := hρ c
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hZP w hwZ u u.2).symm)
    rwa [hcenter, Subgroup.mem_bot] at this
  obtain ⟨ρ', hρ'P, hρ'Z⟩ := exists_hom_sup_of_centralizing hZP ρ hZker
  have hdec : ∀ e ∈ E, ∃ z ∈ Z₀, ∃ x ∈ P, ψ e = z * x := by
    intro e he
    obtain ⟨hψeH, hψeθ⟩ := hψE e he
    have hpow : (ψ e) ^ p = 1 := by rw [← map_pow, hE.2 e he, map_one]
    obtain ⟨z, hzH, hzθ, hzc, x, hxP, hx⟩ := exists_central_mul_of_pow_prime θ hp3 hpp hH hθH hθQ
      hθZ h4 h5 h6 hψeH hψeθ hpow
    exact ⟨z, (hmemZ₀ z).2 ⟨hzH, hzθ, hzc⟩, x, hxP, hx⟩
  have hmemM : ∀ e : E, ψ e ∈ Z₀ ⊔ P := by
    intro e
    obtain ⟨z, hz, x, hx, h⟩ := hdec e e.2
    rw [h]
    exact (Z₀ ⊔ P).mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hx)
  let β : E →* Cat ⟨.twistedA 5 q, hv⟩ :=
    ρ'.comp ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM)
  have hβ : ∀ (e : E) (z x : M) (hz : z ∈ Z₀) (hx : x ∈ P), ψ e = z * x → β e = ρ ⟨x, hx⟩ := by
    intro e z x hz hx h
    have : ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM e) =
        ⟨z, Subgroup.mem_sup_left hz⟩ * ⟨x, Subgroup.mem_sup_right hx⟩ := Subtype.ext h
    show ρ' ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM e) = _
    rw [this, map_mul, hρ'Z z hz, one_mul, hρ'P x hx]
  have hψyZ : ψ y ∈ Z₀ := (hmemZ₀ _).2 ⟨(hψE y hy).1, (hψE y hy).2, hψy⟩
  have hβy : β ⟨y, hy⟩ = 1 := by
    show ρ' ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM ⟨y, hy⟩) = 1
    have : ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM ⟨y, hy⟩) =
        ⟨ψ y, Subgroup.mem_sup_left hψyZ⟩ := rfl
    rw [this]
    exact hρ'Z _ hψyZ
  set hc : Subgroup G := hyperClosure p (⊤ : Subgroup G) E with hhc
  have hcentE : ∀ a : G, (∀ e ∈ E, a * e = e * a) → a ∈ hc := by
    intro a ha
    refine mem_hyperClosure_of_dvd_card hpp hEc ?_
    have hle : E ≤ Subgroup.centralizer {a} := fun e he m hm => by
      rw [Set.mem_singleton_iff.1 hm]; exact ha e he
    rw [inf_eq_left.2 hle, hEc]
    exact pow_dvd_pow p (by norm_num)
  intro k hk
  have hk' : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 hk
  by_cases hcard : Nat.card β.range = p ^ 2
  ·
    set L : Subgroup G := P.comap ψ with hL
    let ρL : L →* Cat ⟨.twistedA 5 q, hv⟩ := ρ.comp (ψ.subgroupComap P)
    have hρL : Function.Surjective ρL := by
      intro c
      obtain ⟨u, rfl⟩ := hρ c
      obtain ⟨g, hg⟩ := hPψ u u.2
      refine ⟨⟨g, by rw [hL, Subgroup.mem_comap, hg]; exact u.2⟩, ?_⟩
      show ρ ⟨ψ g, _⟩ = ρ u
      congr 1
      exact Subtype.ext hg
    have hLy : ∀ l ∈ L, l * y = y * l := by
      intro l hl
      apply hψ
      rw [map_mul, map_mul]
      exact (hψy (ψ l) (hPQ hl)).symm
    have hcomm : ∀ (e : E) (l : L), ρL l * β e = β e * ρL l → (l : G) * e = e * (l : G) := by
      intro e l h
      obtain ⟨z, hz, x, hx, hψe⟩ := hdec e e.2
      have hβe := hβ e z x hz hx hψe
      have hpow : (ψ e) ^ p = 1 := by rw [← map_pow, hE.2 e e.2, map_one]
      have h' : ρ ⟨x, hx⟩ * ρ ⟨ψ l, l.2⟩ = ρ ⟨ψ l, l.2⟩ * ρ ⟨x, hx⟩ := by
        rw [← hβe]; exact h.symm
      have := commute_of_decomp hpp hp3 ρ hkc hkcard hZP hZker hψe hz hx l.2 hpow h'
      apply hψ
      rw [map_mul, map_mul]
      exact this.symm
    have hLhc : L ≤ hc :=
      layer_le_hyperClosure_of_plane hpp hp3' hv hpq E hE hEc hy hy1 L hLy ρL hρL β hβy hcard hcomm
    obtain ⟨hmN, hθm⟩ := hψN k hk'
    obtain ⟨a, haH, hθa, x, hxP, hax⟩ := exists_split_of_fixed θ hH hHQ hθH hθQ hlang hΓ hmN hθm
    obtain ⟨g, hg⟩ := hPψ x hxP
    have hgL : g ∈ L := by rw [hL, Subgroup.mem_comap, hg]; exact hxP
    have ha' : ψ (k * g⁻¹) = a := by
      rw [map_mul, map_inv, hg, hax]; group
    have hcE : k * g⁻¹ ∈ hc := by
      refine hcentE _ fun e he => ?_
      apply hψ
      rw [map_mul ψ (k * g⁻¹) e, map_mul ψ e (k * g⁻¹), ha']
      exact hH a haH _ (hψE e he).1
    have : k = (k * g⁻¹) * g := by group
    rw [this]
    exact hc.mul_mem hcE (hLhc hgL)
  ·
    have hker : ∃ e : E, (e : G) ∉ Subgroup.zpowers y ∧ β e = 1 := by
      have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 3 hpp.ne_zero)
      have hmul := Subgroup.card_ker_mul_card_range β
      obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow hpp).1 (Subgroup.card_range_dvd β |>.trans
        (by rw [hEc]))
      have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
      have hyker : (⟨y, hy⟩ : E) ∈ β.ker := hβy
      have hpker : p ∣ Nat.card β.ker := by
        have h1 : orderOf (⟨y, hy⟩ : E) = p := by
          rw [← hyo, ← Subgroup.orderOf_coe]
        have h2 := orderOf_dvd_natCard (⟨⟨y, hy⟩, hyker⟩ : β.ker)
        rw [Subgroup.orderOf_mk, h1] at h2
        exact h2
      have hi2 : i ≤ 1 := by
        by_contra hgt
        have h3 : i ≤ 3 := hi3
        have : i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl
        · exact hcard hi
        · rw [hi, show p ^ 3 = Nat.card E from hEc.symm] at hmul
          have : Nat.card β.ker = 1 := by
            have hp3pos : 0 < p ^ 3 := pow_pos hpp.pos 3
            nlinarith
          rw [this] at hpker
          exact hpp.one_lt.ne' (Nat.dvd_one.1 hpker)
      have hkerge : p ^ 2 ≤ Nat.card β.ker := by
        have h1 : Nat.card β.range ≤ p := by
          rw [hi]
          calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hpp.pos hi2
            _ = p := pow_one p
        have h2 : p ^ 3 = Nat.card β.ker * Nat.card β.range := by rw [← hEc, ← hmul]
        have : p ^ 3 ≤ Nat.card β.ker * p := by
          calc p ^ 3 = Nat.card β.ker * Nat.card β.range := h2
            _ ≤ Nat.card β.ker * p := Nat.mul_le_mul_left _ h1
        have hp0 : 0 < p := hpp.pos
        have : p ^ 2 * p ≤ Nat.card β.ker * p := by rwa [← pow_succ]
        exact Nat.le_of_mul_le_mul_right this hp0
      by_contra hno
      push Not at hno
      have hsub : (β.ker : Set E) ⊆ (Subgroup.zpowers (⟨y, hy⟩ : E) : Set E) := by
        intro e he
        by_contra hnot
        have := hno e (fun hmem => hnot (by
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
          exact Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩))
        exact this he
      have hcardle : Nat.card β.ker ≤ Nat.card (Subgroup.zpowers (⟨y, hy⟩ : E)) :=
        Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
      rw [Nat.card_zpowers] at hcardle
      have h1 : orderOf (⟨y, hy⟩ : E) = p := by
        rw [← hyo, ← Subgroup.orderOf_coe]
      rw [h1] at hcardle
      have : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
      omega
    obtain ⟨e, hey, hβe⟩ := hker
    obtain ⟨z, hz, x, hx, hψe⟩ := hdec e e.2
    have hρx : ρ ⟨x, hx⟩ = 1 := by rw [← hβ e z x hz hx hψe]; exact hβe
    have hxker : (⟨x, hx⟩ : P) ∈ ρ.ker := hρx
    have hxZ : x ∈ Z₀ := by
      have hfr := hfree x (Subgroup.mem_sup_right (hPQ hx)) (fun u hu => by
        have := hkc ⟨x, hx⟩ hxker ⟨u, hu⟩
        exact congrArg Subtype.val this)
      exact (hmemZ₀ x).2 ⟨hfr.1, hPfix x hx, fun g hg => hfr.2 g hg⟩
    have heZ : ψ e ∈ Z₀ := by rw [hψe]; exact Z₀.mul_mem hz hxZ
    obtain ⟨hmN, -⟩ := hψN k hk'
    have hcent : H ⊔ Q ≤ Subgroup.centralizer {ψ e} := by
      refine sup_le (fun h hh m hm => ?_) (fun g hg m hm => ?_)
      · rw [Set.mem_singleton_iff.1 hm]
        exact (hH _ ((hmemZ₀ _).1 heZ).1 h hh)
      · rw [Set.mem_singleton_iff.1 hm]
        exact ((hmemZ₀ _).1 heZ).2.2 g hg
    have hke : k * e = e * k := by
      apply hψ
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hmN)
    exact mem_hyperClosure_of_commute_pair hE hEc hy e.2 hy1 hey hk' hke

end Main

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

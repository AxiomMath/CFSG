module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResAssemblyB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResAssemblyA

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

variable {Y : Type} [Group Y] [Finite Y] {Cc : Type} [Group Cc]

theorem false_of_layer (hFT : OddSolv) (hH1 : ElemAbH1) (hH2 : ElemAbH2)
    (hCc : Nat.card (MulAut Cc) ∣ gl12) (ρ : Y →* MulAut Cc) (hQodd : Odd (Nat.card ρ.ker))
    (z : Y) (hz2 : z * z = 1) (hQz : ∀ k ∈ ρ.ker, z * k = k * z → k = 1)
    (T : Subgroup Y) (hTz : ∀ t ∈ T, z * t = t * z) (hTperf : commutator T = ⊤)
    (hT1080 : Nat.card T = 1080) (hTw : ∃ w ∈ T, orderOf w = 3 ∧ ∀ t ∈ T, t * w = w * t)
    (hlat : ∀ M : Subgroup Y, (∀ m ∈ M, z * m = m * z) →
      (∀ g : Y, z * g = g * z → ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      (∀ t ∈ T, t ∈ M) ∨ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hT5 : ∀ H : Subgroup (MulAut Cc), (∀ h ∈ H, ∀ t ∈ T, h * ρ t = ρ t * h) →
      Nat.card H ≤ 256)
    (U : Subgroup Y) [U.Normal] (hU : commutator U = ⊤) {E : Type} [Group E] [Finite E]
    (q : U →* E) (hq : Function.Surjective q) (hqodd : Odd (Nat.card q.ker))
    (hker : ∀ u : U, ρ u = 1 → q u = 1) (hE : EData E) : False := by
  obtain ⟨e₁, he₁⟩ := exists_mulEquiv_range hFT hH1 hH2 hCc ρ U hU q hq hqodd hker hE
  set Ut : Subgroup (MulAut Cc) := (ρ.comp U.subtype).range with hUt
  have hmemUt : ∀ x : MulAut Cc, x ∈ Ut ↔ ∃ u : U, ρ u = x := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
  have hnorm : ∀ y : Y, ∀ x ∈ Ut, ρ y * x * (ρ y)⁻¹ ∈ Ut := by
    intro y x hx
    obtain ⟨u, rfl⟩ := (hmemUt x).1 hx
    refine (hmemUt _).2 ⟨⟨y * u * y⁻¹, Normal.conj_mem inferInstance (u : Y) u.2 y⟩, ?_⟩
    simp [map_mul, map_inv]
  have hnorm' : ∀ y : Y, ∀ x ∈ Ut, (ρ y)⁻¹ * x * ρ y ∈ Ut := by
    intro y x hx
    have := hnorm y⁻¹ x hx
    simpa [map_inv] using this
  have hcenterUt : ∀ c ∈ Ut, (∀ u ∈ Ut, c * u = u * c) → c = 1 := by
    intro c hc hcc
    have hc1 : e₁ ⟨c, hc⟩ = 1 := by
      apply hE.chief.center
      intro x
      obtain ⟨a, rfl⟩ := e₁.surjective x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcc a.1 a.2).symm
    have : (⟨c, hc⟩ : Ut) = 1 := e₁.injective (by rw [hc1, map_one])
    exact congrArg Subtype.val this
  have hout : Group.IsSolvable (Outer Ut) :=
    have := hE.outer
    Group.isSolvable_of_surjective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e₁.symm).surjective
  let R : Subgroup (MulAut Cc) := Subgroup.centralizer (Ut : Set (MulAut Cc))
  have hmemR : ∀ r : MulAut Cc, r ∈ R ↔ ∀ u ∈ Ut, u * r = r * u := fun r =>
    Subgroup.mem_centralizer_iff
  have hnormR : ∀ y : Y, ∀ r ∈ R, ρ y * r * (ρ y)⁻¹ ∈ R := by
    intro y r hr u hu
    have h1 := (hmemR r).1 hr _ (hnorm' y u hu)
    show u * (ρ y * r * (ρ y)⁻¹) = ρ y * r * (ρ y)⁻¹ * u
    have e1 : u = ρ y * ((ρ y)⁻¹ * u * ρ y) * (ρ y)⁻¹ := by group
    calc u * (ρ y * r * (ρ y)⁻¹)
        = ρ y * (((ρ y)⁻¹ * u * ρ y) * r) * (ρ y)⁻¹ := by group
      _ = ρ y * (r * ((ρ y)⁻¹ * u * ρ y)) * (ρ y)⁻¹ := by rw [h1]
      _ = ρ y * r * (ρ y)⁻¹ * u := by group
  let Uh : Subgroup Y := Ut.comap ρ
  let Rh : Subgroup Y := R.comap ρ
  have hUhn : Uh.Normal := ⟨fun n hn g => by
    show ρ (g * n * g⁻¹) ∈ Ut
    rw [map_mul, map_mul, map_inv]
    exact hnorm g _ hn⟩
  have hRhn : Rh.Normal := ⟨fun n hn g => by
    show ρ (g * n * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hnormR g _ hn⟩
  let Γ : Subgroup Y := Subgroup.centralizer ({z} : Set Y)
  have hΓ : ∀ y : Y, y ∈ Γ ↔ z * y = y * z := fun y => by
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
  let M₁ : Subgroup Y := Uh ⊓ Γ
  let M₂ : Subgroup Y := Rh ⊓ Γ
  have hM₁z : ∀ m ∈ M₁, z * m = m * z := fun m hm => (hΓ m).1 hm.2
  have hM₂z : ∀ m ∈ M₂, z * m = m * z := fun m hm => (hΓ m).1 hm.2
  have hM₁n : ∀ g : Y, z * g = g * z → ∀ m ∈ M₁, g * m * g⁻¹ ∈ M₁ := by
    intro g hg m hm
    refine ⟨hUhn.conj_mem m hm.1 g, (hΓ _).2 ?_⟩
    have := (hΓ m).1 hm.2
    calc z * (g * m * g⁻¹) = (z * g) * m * g⁻¹ := by group
      _ = g * (z * m) * g⁻¹ := by rw [hg]; group
      _ = g * (m * z) * g⁻¹ := by rw [this]
      _ = g * m * (z * g⁻¹) := by group
      _ = g * m * (g⁻¹ * z) := by
        have : z * g⁻¹ = g⁻¹ * z := by
          calc z * g⁻¹ = g⁻¹ * (g * z) * g⁻¹ := by group
            _ = g⁻¹ * (z * g) * g⁻¹ := by rw [hg]
            _ = g⁻¹ * z := by group
        rw [this]
      _ = g * m * g⁻¹ * z := by group
  have hM₂n : ∀ g : Y, z * g = g * z → ∀ m ∈ M₂, g * m * g⁻¹ ∈ M₂ := by
    intro g hg m hm
    refine ⟨hRhn.conj_mem m hm.1 g, (hΓ _).2 ?_⟩
    have := (hΓ m).1 hm.2
    calc z * (g * m * g⁻¹) = (z * g) * m * g⁻¹ := by group
      _ = g * (z * m) * g⁻¹ := by rw [hg]; group
      _ = g * (m * z) * g⁻¹ := by rw [this]
      _ = g * m * (z * g⁻¹) := by group
      _ = g * m * (g⁻¹ * z) := by
        have : z * g⁻¹ = g⁻¹ * z := by
          calc z * g⁻¹ = g⁻¹ * (g * z) * g⁻¹ := by group
            _ = g⁻¹ * (z * g) * g⁻¹ := by rw [hg]
            _ = g⁻¹ * z := by group
        rw [this]
      _ = g * m * g⁻¹ * z := by group
  have hperfT : Group.IsPerfect T := ⟨hTperf⟩
  let α : T →* MulAut Ut :=
    { toFun := fun t => conjAct Ut (ρ t) (hnorm t) (hnorm' t)
      map_one' := by
        apply MulEquiv.ext
        intro u
        apply Subtype.ext
        simp [conjAct_apply]
      map_mul' := fun a b => by
        apply MulEquiv.ext
        intro u
        apply Subtype.ext
        simp [conjAct_apply, mul_assoc] }
  have hdec : ∀ t ∈ T, ∃ a ∈ M₁, ∃ b ∈ M₂, t = a * b := by
    intro t ht
    obtain ⟨e, he⟩ := exists_conj_of_perfect hout α ⟨t, ht⟩
    have he' : ∀ u ∈ Ut, ρ t * u * (ρ t)⁻¹ = (e : MulAut Cc) * u * (e : MulAut Cc)⁻¹ := by
      intro u hu
      have := congrArg (fun φ : MulAut Ut => ((φ ⟨u, hu⟩ : Ut) : MulAut Cc)) he
      simpa [α, conjAct_apply, MulAut.conj_apply] using this
    set r : MulAut Cc := (e : MulAut Cc)⁻¹ * ρ t with hr
    have hrR : r ∈ R := by
      rw [hmemR]
      intro u hu
      have h1 := he' u hu
      have h2 : ρ t * u = (e : MulAut Cc) * u * (e : MulAut Cc)⁻¹ * ρ t := by
        rw [← h1]; group
      calc u * r = (e : MulAut Cc)⁻¹ * ((e : MulAut Cc) * u * (e : MulAut Cc)⁻¹ * ρ t) := by
            rw [hr]; group
        _ = (e : MulAut Cc)⁻¹ * (ρ t * u) := by rw [h2]
        _ = r * u := by rw [hr]; group
    obtain ⟨û₀, hû₀⟩ := (hmemUt (e : MulAut Cc)).1 e.2
    obtain ⟨û, hû⟩ : ∃ û : Y, ρ û = (e : MulAut Cc) := ⟨û₀, hû₀⟩
    have hν : ρ z * ρ t = ρ t * ρ z := by rw [← map_mul, ← map_mul, hTz t ht]
    have hze : ρ z * (e : MulAut Cc) * (ρ z)⁻¹ = (e : MulAut Cc) := by
      set e' : MulAut Cc := ρ z * (e : MulAut Cc) * (ρ z)⁻¹ with he'def
      have he'Ut : e' ∈ Ut := hnorm z _ e.2
      have hr'R : ρ z * r * (ρ z)⁻¹ ∈ R := hnormR z r hrR
      have hprod : e' * (ρ z * r * (ρ z)⁻¹) = ρ t := by
        calc e' * (ρ z * r * (ρ z)⁻¹) = ρ z * ((e : MulAut Cc) * r) * (ρ z)⁻¹ := by
              rw [he'def]; group
          _ = ρ z * ρ t * (ρ z)⁻¹ := by rw [hr]; group
          _ = ρ t := by rw [hν]; group
      have hpe : (e : MulAut Cc) * r = ρ t := by rw [hr]; group
      have hX : (e : MulAut Cc)⁻¹ * e' = r * (ρ z * r * (ρ z)⁻¹)⁻¹ := by
        have : e' * (ρ z * r * (ρ z)⁻¹) = (e : MulAut Cc) * r := by rw [hprod, hpe]
        calc (e : MulAut Cc)⁻¹ * e' = (e : MulAut Cc)⁻¹ * (e' * (ρ z * r * (ρ z)⁻¹)) *
              (ρ z * r * (ρ z)⁻¹)⁻¹ := by group
          _ = r * (ρ z * r * (ρ z)⁻¹)⁻¹ := by rw [this]; group
      have hXUt : (e : MulAut Cc)⁻¹ * e' ∈ Ut := mul_mem (inv_mem e.2) he'Ut
      have hXR : (e : MulAut Cc)⁻¹ * e' ∈ R := by rw [hX]; exact mul_mem hrR (inv_mem hr'R)
      have h1 : (e : MulAut Cc)⁻¹ * e' = 1 :=
        hcenterUt _ hXUt fun u hu => ((hmemR _).1 hXR u hu).symm
      calc e' = (e : MulAut Cc) * ((e : MulAut Cc)⁻¹ * e') := by group
        _ = (e : MulAut Cc) := by rw [h1, mul_one]
    have hcom : z * û * z⁻¹ * û⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hû]
      rw [hze]
      group
    obtain ⟨k, hk, hzk⟩ := exists_fixed_in_coset ρ.ker hQodd hz2 hcom
    have hρa : ρ (û * k) = (e : MulAut Cc) := by
      rw [map_mul, hû, MonoidHom.mem_ker.1 hk, mul_one]
    refine ⟨û * k, ⟨?_, (hΓ _).2 hzk⟩, (û * k)⁻¹ * t, ⟨?_, (hΓ _).2 ?_⟩, by group⟩
    · show ρ (û * k) ∈ Ut
      rw [hρa]; exact e.2
    · show ρ ((û * k)⁻¹ * t) ∈ R
      rw [map_mul, map_inv, hρa]
      exact hrR
    · have h1 := hzk
      have h2 := hTz t ht
      calc z * ((û * k)⁻¹ * t) = ((û * k)⁻¹ * (û * k)) * z * ((û * k)⁻¹ * t) := by group
        _ = (û * k)⁻¹ * ((û * k) * z) * ((û * k)⁻¹ * t) := by group
        _ = (û * k)⁻¹ * (z * (û * k)) * ((û * k)⁻¹ * t) := by rw [h1]
        _ = (û * k)⁻¹ * z * t := by group
        _ = (û * k)⁻¹ * (t * z) := by rw [mul_assoc, h2]
        _ = (û * k)⁻¹ * t * z := by group
  have hint : ∀ y ∈ M₁, y ∈ M₂ → y = 1 := by
    intro y hy1 hy2
    have hy : ρ y = 1 := by
      apply hcenterUt _ hy1.1
      intro u hu
      exact ((hmemR _).1 hy2.1 u hu).symm
    exact hQz y hy ((hΓ y).1 hy1.2)
  have hcomm : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := by
    intro a ha b hb
    have h1 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := by
      have := (hmemR _).1 hb.1 _ ha.1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹ = (ρ a * ρ b) * (ρ a)⁻¹ * (ρ b)⁻¹ := by group
        _ = (ρ b * ρ a) * (ρ a)⁻¹ * (ρ b)⁻¹ := by rw [← this]
        _ = 1 := by group
    have h2 : z * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * z := by
      have hza := (hΓ a).1 ha.2
      have hzb := (hΓ b).1 hb.2
      have hzai : z * a⁻¹ = a⁻¹ * z := by
        calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
          _ = a⁻¹ * (z * a) * a⁻¹ := by rw [hza]
          _ = a⁻¹ * z := by group
      have hzbi : z * b⁻¹ = b⁻¹ * z := by
        calc z * b⁻¹ = b⁻¹ * (b * z) * b⁻¹ := by group
          _ = b⁻¹ * (z * b) * b⁻¹ := by rw [hzb]
          _ = b⁻¹ * z := by group
      calc z * (a * b * a⁻¹ * b⁻¹) = (z * a) * b * a⁻¹ * b⁻¹ := by group
        _ = a * (z * b) * a⁻¹ * b⁻¹ := by rw [hza]; group
        _ = a * b * (z * a⁻¹) * b⁻¹ := by rw [hzb]; group
        _ = a * b * (a⁻¹ * z) * b⁻¹ := by rw [hzai]
        _ = a * b * a⁻¹ * (z * b⁻¹) := by group
        _ = a * b * a⁻¹ * (b⁻¹ * z) := by rw [hzbi]
        _ = (a * b * a⁻¹ * b⁻¹) * z := by group
    have h3 := hQz _ (MonoidHom.mem_ker.2 h1) h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hcard_Ut : Nat.card Ut = Nat.card E := Nat.card_congr e₁.toEquiv
  by_cases hT1 : ∀ t ∈ T, t ∈ M₁
  ·
    have hmem : ∀ t : T, ρ t ∈ Ut := fun t => (hT1 t t.2).1
    let τ : T →* Ut := (ρ.comp T.subtype).codRestrict Ut hmem
    let ε : T →* E := e₁.toMonoidHom.comp τ
    have hinj : Function.Injective ε := by
      rw [injective_iff_map_eq_one]
      intro t ht
      have h1 : τ t = 1 := e₁.injective (by simpa [ε] using ht)
      have h2 : ρ t = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      exact hQz t h2 (hTz t t.2)
    obtain ⟨w, hwT, hw3, hwc⟩ := hTw
    refine hE.no3A6 ε.range ((Group.IsPerfect.range ε).commutator_eq_top) ?_ (ε ⟨w, hwT⟩)
      ⟨⟨w, hwT⟩, rfl⟩ ?_ ?_
    · rw [← hT1080]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    · rw [orderOf_injective ε hinj, Subgroup.orderOf_mk, hw3]
    · rintro _ ⟨t, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hwc t t.2)
  · have hab1 : ∀ a ∈ M₁, ∀ b ∈ M₁, a * b = b * a :=
      (hlat M₁ hM₁z hM₁n).resolve_left hT1
    by_cases hT2 : ∀ t ∈ T, t ∈ M₂
    ·
      have h256 := hT5 Ut (fun h hh t ht => ((hmemR _).1 (hT2 t ht).1 h hh)) 
      have := hE.big
      omega
    · have hab2 : ∀ a ∈ M₂, ∀ b ∈ M₂, a * b = b * a :=
        (hlat M₂ hM₂z hM₂n).resolve_left hT2
      have hTab : ∀ s t : T, s * t = t * s := by
        intro s t
        obtain ⟨a, ha, b, hb, hst⟩ := hdec s s.2
        obtain ⟨a', ha', b', hb', hts⟩ := hdec t t.2
        apply Subtype.ext
        show (s : Y) * t = t * s
        rw [hst, hts]
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hcomm a' ha' b hb]
          _ = (a * a') * (b * b') := by group
          _ = (a' * a) * (b' * b) := by rw [hab1 a ha a' ha', hab2 b hb b' hb']
          _ = a' * (a * b') * b := by group
          _ = a' * (b' * a) * b := by rw [hcomm a ha b' hb']
          _ = a' * b' * (a * b) := by group
      have hbot : (commutator T) ≤ ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        exact hTab a b
      rw [hTperf] at hbot
      have : Subsingleton T := ⟨fun a b => by
        have ha : a ∈ (⊥ : Subgroup T) := hbot (mem_top a)
        have hb : b ∈ (⊥ : Subgroup T) := hbot (mem_top b)
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
      have h1 : Nat.card T = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
      omega

end CFSG.EvenSporadicStandard.M24Std

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutSpec2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SylowConj

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv CFSG.RankThree.Native

@[expose] def OuterData {W : Type*} [Group W] (Q Sw : Subgroup W) (zw : W) : Prop :=
  ∃ (yw sw : W) (ψ : Perm (Fin 8) →* W), yw ∈ Sw ∧ yw ∉ Q ∧ yw * yw = 1 ∧ sw ∈ Sw ∧
    sw * yw * sw⁻¹ = yw * zw ∧ Function.Injective ψ ∧
    ψ.range = centralizer ({yw} : Set W) ⊓ Q ∧
    (∃ σ₀ ∈ alternatingGroup (Fin 8), ψ σ₀ = zw) ∧
    (∃ κ ∉ alternatingGroup (Fin 8), ψ κ * zw = zw * ψ κ) ∧
    (∀ σ, ψ σ * zw = zw * ψ σ → ψ σ ^ 5 = 1 → ψ σ = 1) ∧
    Q ≤ (alternatingGroup (Fin 8)).map ψ ⊔
      ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj sw).toMonoidHom ∧
    ∀ x ∈ Sw, x * x = 1 → x ≠ 1 → ∃ r : W, r ^ 5 = 1 ∧ r ≠ 1 ∧ r * x = x * r

theorem OuterData.conj {W : Type*} [Group W] {Q S₀ : Subgroup W} [Q.Normal] {z₀ : W}
    (h : OuterData Q S₀ z₀) (g : W) (Sw : Subgroup W) (hS : ∀ y, y ∈ Sw ↔ g⁻¹ * y * g ∈ S₀) :
    OuterData Q Sw (g * z₀ * g⁻¹) := by
  obtain ⟨y, s, ψ, hyS, hyQ, hy2, hsS, hsy, hψ, hrange, ⟨σ₀, hσ₀, hz⟩, ⟨κ, hκ, hκz⟩, hF2, hgen,
    hF1⟩ := h
  have hQc : ∀ x : W, g * x * g⁻¹ ∈ Q ↔ x ∈ Q := by
    intro x
    constructor
    · intro hx
      have := (inferInstance : Q.Normal).conj_mem _ hx g⁻¹
      simpa [mul_assoc] using this
    · intro hx
      exact (inferInstance : Q.Normal).conj_mem _ hx g
  have hQc' : ∀ x : W, g⁻¹ * x * g ∈ Q ↔ x ∈ Q := by
    intro x
    have := hQc (g⁻¹ * x * g)
    simpa [mul_assoc] using this.symm.trans (by simp [mul_assoc])
  have hSS : ∀ x : W, g * x * g⁻¹ ∈ Sw ↔ x ∈ S₀ := fun x => by
    rw [hS]
    simp [mul_assoc]
  set c : W →* W := (MulAut.conj g).toMonoidHom with hc
  have hcapp : ∀ x : W, c x = g * x * g⁻¹ := fun x => rfl
  refine ⟨g * y * g⁻¹, g * s * g⁻¹, c.comp ψ, (hSS y).2 hyS, fun h => hyQ ((hQc y).1 h), ?_,
    (hSS s).2 hsS, ?_, (MulAut.conj g).injective.comp hψ, ?_, ⟨σ₀, hσ₀, ?_⟩,
    ⟨κ, hκ, ?_⟩, ?_, ?_, ?_⟩
  · calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  · calc g * s * g⁻¹ * (g * y * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * y * s⁻¹) * g⁻¹ := by group
      _ = g * (y * z₀) * g⁻¹ := by rw [hsy]
      _ = g * y * g⁻¹ * (g * z₀ * g⁻¹) := by group
  · ext x
    constructor
    · rintro ⟨σ, rfl⟩
      have h1 : ψ σ ∈ centralizer ({y} : Set W) ⊓ Q := hrange ▸ ⟨σ, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.2 ?_, (hQc _).2 h1.2⟩
      have := mem_centralizer_singleton_iff.1 h1.1
      show g * ψ σ * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * ψ σ * g⁻¹)
      calc g * ψ σ * g⁻¹ * (g * y * g⁻¹) = g * (ψ σ * y) * g⁻¹ := by group
        _ = g * (y * ψ σ) * g⁻¹ := by rw [this]
        _ = g * y * g⁻¹ * (g * ψ σ * g⁻¹) := by group
    · rintro ⟨h1, h2⟩
      have h3 : g⁻¹ * x * g ∈ ψ.range := by
        rw [hrange]
        refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
        · have := mem_centralizer_singleton_iff.1 h1
          calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [this]
            _ = y * (g⁻¹ * x * g) := by group
        · have := (hQc (g⁻¹ * x * g)).1 (by simpa [mul_assoc] using h2)
          exact this
      obtain ⟨σ, hσ⟩ := h3
      exact ⟨σ, by simp only [MonoidHom.comp_apply]; rw [hcapp, hσ]; group⟩
  · simp only [MonoidHom.comp_apply, hz]
    rfl
  · simp only [MonoidHom.comp_apply]
    show g * ψ κ * g⁻¹ * (g * z₀ * g⁻¹) = g * z₀ * g⁻¹ * (g * ψ κ * g⁻¹)
    calc g * ψ κ * g⁻¹ * (g * z₀ * g⁻¹) = g * (ψ κ * z₀) * g⁻¹ := by group
      _ = g * (z₀ * ψ κ) * g⁻¹ := by rw [hκz]
      _ = g * z₀ * g⁻¹ * (g * ψ κ * g⁻¹) := by group
  · intro σ h1 h5
    simp only [MonoidHom.comp_apply, hcapp] at h1 h5 ⊢
    have h1' : ψ σ * z₀ = z₀ * ψ σ := by
      have : g * (ψ σ * z₀) * g⁻¹ = g * (z₀ * ψ σ) * g⁻¹ := by
        calc g * (ψ σ * z₀) * g⁻¹ = g * ψ σ * g⁻¹ * (g * z₀ * g⁻¹) := by group
          _ = g * z₀ * g⁻¹ * (g * ψ σ * g⁻¹) := h1
          _ = g * (z₀ * ψ σ) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel this)
    have h5' : ψ σ ^ 5 = 1 := by
      have : g * ψ σ ^ 5 * g⁻¹ = 1 := by rw [← conj_pow]; exact h5
      calc ψ σ ^ 5 = g⁻¹ * (g * ψ σ ^ 5 * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    rw [hF2 σ h1' h5']
    group
  · have h1 : Q ≤ ((alternatingGroup (Fin 8)).map ψ ⊔
        ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom).map c := by
      intro q hq
      refine ⟨g⁻¹ * q * g, hgen ?_, by rw [hcapp]; group⟩
      have := (hQc (g⁻¹ * q * g)).1
      simpa [mul_assoc] using (hQc' q).2 hq
    rw [Subgroup.map_sup] at h1
    have e1 : ((alternatingGroup (Fin 8)).map ψ).map c =
        (alternatingGroup (Fin 8)).map (c.comp ψ) :=
      Subgroup.map_map _ _ _
    have hcomm : c.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (g * s * g⁻¹)).toMonoidHom.comp c := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc]
      group
    have e2 : (((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom).map c =
        ((alternatingGroup (Fin 8)).map (c.comp ψ)).map
          (MulAut.conj (g * s * g⁻¹)).toMonoidHom := by
      have l1 : (((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom).map c =
          ((alternatingGroup (Fin 8)).map ψ).map (c.comp (MulAut.conj s).toMonoidHom) :=
        Subgroup.map_map _ _ _
      have l2 : ((alternatingGroup (Fin 8)).map (c.comp ψ)).map
          (MulAut.conj (g * s * g⁻¹)).toMonoidHom =
          ((alternatingGroup (Fin 8)).map ψ).map
            ((MulAut.conj (g * s * g⁻¹)).toMonoidHom.comp c) := by
        rw [← e1]
        exact Subgroup.map_map _ _ _
      rw [l1, l2, hcomm]
    rw [e1, e2] at h1
    exact h1
  · intro x hx hx2 hx1
    have h1 : g⁻¹ * x * g ∈ S₀ := (hS x).1 hx
    have h2 : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
      calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [hx2]; group
    have h3 : g⁻¹ * x * g ≠ 1 := by
      intro h
      apply hx1
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    obtain ⟨r, hr5, hr1, hrc⟩ := hF1 _ h1 h2 h3
    refine ⟨g * r * g⁻¹, ?_, ?_, ?_⟩
    · rw [conj_pow, hr5]
      group
    · intro h
      apply hr1
      calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc g * r * g⁻¹ * x = g * (r * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * r) * g⁻¹ := by rw [hrc]
        _ = x * (g * r * g⁻¹) := by group


theorem hs100_outerBase :
    ∃ (S₀ : Subgroup ↥hs100R) (z₀ : ↥hs100R), IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧
      z₀ ∈ (Subgroup.inclusion hs100P_le_R).range ∧ z₀ ≠ 1 ∧
      (∀ x ∈ S₀ ⊓ (Subgroup.inclusion hs100P_le_R).range, z₀ * x = x * z₀) ∧
      OuterData (Subgroup.inclusion hs100P_le_R).range S₀ z₀ := by
  classical
  obtain ⟨hR, hcard, hzP, hz2, hz1, hzc, hyS, hyP, hy2, hsS, hsy, -, ψ, hψ, hψr, ⟨σ₀, hσ₀, hψz⟩,
    ⟨κ, hκ, hψκ⟩, hF2, hprods⟩ := s5o_spec1
  obtain ⟨hF1, hgen⟩ := s5o_spec2 hR
  set Q : Subgroup ↥hs100R := (Subgroup.inclusion hs100P_le_R).range with hQ
  have hmemQ : ∀ x : ↥hs100R, x ∈ Q ↔ (x : Equiv.Perm (Fin 100)) ∈ hs100P := by
    intro x
    rw [hQ, Subgroup.inclusion_range, mem_subgroupOf]
  set S₀ : Subgroup ↥hs100R := s5oS1.subgroupOf hs100R with hS₀
  have hmemS : ∀ x : ↥hs100R, x ∈ S₀ ↔ (x : Equiv.Perm (Fin 100)) ∈ s5oS1 := fun x =>
    mem_subgroupOf
  have hcard' : Nat.card S₀ = 2 ^ 10 := by
    rw [hS₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv, hcard]
    norm_num
  have hp : IsPGroup 2 S₀ := IsPGroup.of_card hcard'
  have hidx : ¬ 2 ∣ S₀.index := by
    have h := Subgroup.card_mul_index S₀
    rw [hcard', card_hs100R] at h
    omega
  let y' : ↥hs100R := ⟨s5oy, hR hyS⟩
  let s' : ↥hs100R := ⟨s5os, hR hsS⟩
  let z' : ↥hs100R := ⟨s5oz, hs100P_le_R hzP⟩
  have hψR : ∀ σ, ψ σ ∈ hs100R := fun σ =>
    hs100P_le_R ((hψr ▸ ⟨σ, rfl⟩ : ψ σ ∈ centralizer ({s5oy} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100P).2)
  let ψW : Equiv.Perm (Fin 8) →* ↥hs100R := ψ.codRestrict hs100R hψR
  have hψW : ∀ σ, ((ψW σ : ↥hs100R) : Equiv.Perm (Fin 100)) = ψ σ := fun σ => rfl
  have hrange : ψW.range = centralizer ({y'} : Set ↥hs100R) ⊓ Q := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      have h1 : ψ σ ∈ centralizer ({s5oy} : Set (Equiv.Perm (Fin 100))) ⊓ hs100P :=
        hψr ▸ ⟨σ, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.2 (Subtype.ext ?_), (hmemQ _).2 h1.2⟩
      exact mem_centralizer_singleton_iff.1 h1.1
    · rintro ⟨h1, h2⟩
      have h3 : (x : Equiv.Perm (Fin 100)) ∈ ψ.range := by
        rw [hψr]
        exact ⟨mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1)), (hmemQ x).1 h2⟩
      obtain ⟨σ, hσ⟩ := h3
      exact ⟨σ, Subtype.ext hσ⟩
  have hP_le : hs100P ≤ (alternatingGroup (Fin 8)).map ψ ⊔
      ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s5os).toMonoidHom := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Subgroup.mem_sup_left (hprods i (Set.mem_Iio.1 hi))
    · exact Subgroup.mem_sup_right ⟨_, hprods i (Set.mem_Iio.1 hi), rfl⟩
  have hgenW : Q ≤ (alternatingGroup (Fin 8)).map ψW ⊔
      ((alternatingGroup (Fin 8)).map ψW).map (MulAut.conj s').toMonoidHom := by
    set K' := (alternatingGroup (Fin 8)).map ψW ⊔
      ((alternatingGroup (Fin 8)).map ψW).map (MulAut.conj s').toMonoidHom with hK'
    have hsub : hs100R.subtype.comp ψW = ψ := by
      ext σ
      rfl
    have e1 : (alternatingGroup (Fin 8)).map ψ = ((alternatingGroup (Fin 8)).map ψW).map
        hs100R.subtype := by
      rw [Subgroup.map_map, hsub]
    have hcomm : (MulAut.conj s5os).toMonoidHom.comp hs100R.subtype =
        hs100R.subtype.comp (MulAut.conj s').toMonoidHom := by
      ext x
      rfl
    have h1 : (alternatingGroup (Fin 8)).map ψ ≤ K'.map hs100R.subtype := by
      rw [e1]
      exact Subgroup.map_mono le_sup_left
    have h2 : ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s5os).toMonoidHom ≤
        K'.map hs100R.subtype := by
      rw [e1, Subgroup.map_map, hcomm, ← Subgroup.map_map]
      exact Subgroup.map_mono le_sup_right
    have h3 : hs100P ≤ K'.map hs100R.subtype := hP_le.trans (sup_le h1 h2)
    intro q hq
    obtain ⟨k, hk, hkq⟩ := h3 ((hmemQ q).1 hq)
    have : k = q := Subtype.ext hkq
    rw [← this]
    exact hk
  refine ⟨S₀, z', hp, hidx, (hmemQ z').2 hzP, fun h => hz1 (congrArg Subtype.val h),
    fun x hx => Subtype.ext (hzc x.1 ((hmemS x).1 hx.1) ((hmemQ x).1 hx.2)),
    y', s', ψW, (hmemS _).2 hyS, fun h => hyP ((hmemQ _).1 h), Subtype.ext hy2, (hmemS _).2 hsS,
    Subtype.ext hsy, fun a b h => hψ (congrArg Subtype.val h), hrange, ⟨σ₀, hσ₀, Subtype.ext hψz⟩,
    ⟨κ, hκ, Subtype.ext hψκ⟩, ?_, hgenW, ?_⟩
  · intro σ h1 h5
    exact Subtype.ext (hF2 σ (congrArg Subtype.val h1) (congrArg Subtype.val h5))
  · intro x hx hx2 hx1
    obtain ⟨r, hrR, hr5, hr1, hrc⟩ := hF1 x.1 ((hmemS x).1 hx) (congrArg Subtype.val hx2)
      (fun h => hx1 (Subtype.ext h))
    exact ⟨⟨r, hrR⟩, Subtype.ext hr5, fun h => hr1 (congrArg Subtype.val h), Subtype.ext hrc⟩

@[expose] def HS100OuterData : Prop :=
  ∀ Sw : Subgroup ↥hs100R, IsPGroup 2 Sw → ¬ 2 ∣ Sw.index → ∀ zw : ↥hs100R,
    orderOf zw = 2 →
    centralizer ((Sw ⊓ (Subgroup.inclusion hs100P_le_R).range : Subgroup ↥hs100R) :
      Set ↥hs100R) ⊓ (Subgroup.inclusion hs100P_le_R).range = zpowers zw →
    OuterData (Subgroup.inclusion hs100P_le_R).range Sw zw

theorem hs100Outer :
    HS100OuterData := by
  obtain ⟨S₀, z₀, hp, hidx, hz₀Q, hz₀1, hz₀c, hdata⟩ := hs100_outerBase
  have hQn : ((Subgroup.inclusion hs100P_le_R).range).Normal := by
    rw [Subgroup.inclusion_range]
    exact hs100P_normal_R
  intro Sw hSw hSwi zw hzw2 hcent
  obtain ⟨g, hmem, hz'⟩ := exists_conj_of_one_sylow _ S₀ hp hidx z₀ hz₀Q hz₀1 hz₀c Sw hSw hSwi zw
    hzw2 hcent
  have := hdata.conj g Sw hmem
  rw [hz'] at this
  exact this

end CFSG.EvenSporadicStandard.HSStd

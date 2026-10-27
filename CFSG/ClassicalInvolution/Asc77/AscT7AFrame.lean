module

public import CFSG.ClassicalInvolution.Asc77.AscT7ATwin
public import CFSG.ClassicalInvolution.Asc77.AscT7AEStand
public import CFSG.ClassicalInvolution.Asc77.AscE184SecB
public import CFSG.ClassicalInvolution.Asc77.AscE187Conj

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

theorem exists_commuting_sylow_twin (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  obtain ⟨R', hR', hfix⟩ := exists_sylow_normalized hR.2.1 (hR.1.trans hKN)
  have hRn : R ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  have h2 : IsPGroup 2 ↥(R ⊔ R') := hR.2.1.to_sup_of_normal_right' hR'.2.1 hRn
  exact ⟨R, R', hR, hR', hΩ.commutes_of_twin_of_isPGroup hK hK' hne.symm hz hz' hR.1 hR'.1 h2⟩

theorem exists_sylow_pair_of_mem (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧ u ∈ R ⊔ R' := by
  obtain ⟨R₀, R₀', hR₀, hR₀', hc₀⟩ := exists_commuting_sylow_twin hΩ hK hK' hne hz hz'
  have hQ₀ := isSylow2In_sup_of_twin hp hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨P, hP, huP⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self_eq_one hu2 hu1)
    (Subgroup.zpowers_le.mpr hu)
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hP
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  refine ⟨conjSub g R₀, conjSub g R₀', ?_, ?_, hc₀.conjSub g, ?_⟩
  · have := hR₀.conj g
    rwa [hgK] at this
  · have := hR₀'.conj g
    rwa [hgK'] at this
  · rw [← conjSub_sup_eq, hg]
    exact huP (Subgroup.mem_zpowers u)

end T7A

theorem exists_twinFrameData_at (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J' : Subgroup G} {z u t' : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K)) (ht' : IsUniqueInvolution J' t') :
    ∃ g ∈ K ⊔ K', ∃ W : Subgroup G, TwinFrameData Ω K K' z u (conjSub g J') (g * t' * g⁻¹) ∧
      W ∈ WSet Ω ∧ z ∈ W ∧ g * t' * g⁻¹ ∈ W := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    T7A.exists_sylow_pair_of_mem hp hΩ hK hK'Ω hne hz hzK' hu hu2 hu1
  obtain ⟨g, hgQ, W, hJ'', ht'', hW, hzW, htW, hfr⟩ :=
    exists_twinFrameData_of_sylows hp hq hΩ hK hz hK' hne hJ' ht' hR₁ hR₂ hc
  obtain ⟨x, hx, y, hy, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  have hcxy : x * y = y * x := hc x hx y hy
  have hsq : (x * x) * (y * y) = 1 := by
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hcxy]
      _ = (x * y) * (x * y) := by group
      _ = 1 := hu2
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have hxxA : x * x ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem hx hx, ?_⟩
    have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hy hy)
  have hx2 : x * x = z := by
    rcases hz.unique (x * x) (K.mul_mem hxK hxK) (hA _ hxxA) with h1 | h1
    · exfalso
      have hy2 : y * y = 1 := by rwa [h1, one_mul] at hsq
      rcases hz.unique x hxK h1 with h2 | h2 <;> rcases hzK'.unique y hyK' hy2 with h3 | h3
      · exact hu1 (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, mul_one])
      · exact hu1 (by rw [h2, h3]; exact hz.sq)
    · exact h1
  have hy2 : y * y = z := by
    have h1 : y * y = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [hx2] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz.sq
  exact ⟨g, hgQ, W, hfr x hx y hy (T7A.orderOf_eq_four_of_sq hz hx2)
    (T7A.orderOf_eq_four_of_sq hz hy2), hW, hzW, htW⟩


omit [Finite G] in
theorem T7A.conjSub_centralizer_singleton_eq (g a : G) :
    conjSub g (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * x := by group
  · intro h
    calc (g⁻¹ * x * g) * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [h]
      _ = a * (g⁻¹ * x * g) := by group

omit [Finite G] in
theorem T7A.oddCoreOf_centralizer_conj (g a : G) :
    oddCoreOf (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) =
      conjSub g (oddCoreOf (Subgroup.centralizer ({a} : Set G))) := by
  rw [← T7A.conjSub_centralizer_singleton_eq, AscE184Sect.oddCoreOf_conjSub]

omit [Finite G] in
theorem T7A.conjSub_iInf {ι : Sort*} (g : G) (A : ι → Subgroup G) :
    conjSub g (⨅ i, A i) = ⨅ i, conjSub g (A i) := by
  let e : Subgroup G ≃o Subgroup G :=
    { toFun := conjSub g
      invFun := conjSub g⁻¹
      left_inv := conjSub_inv_conjSub g
      right_inv := conjSub_conjSub_inv g
      map_rel_iff' := by
        intro X Y
        show conjSub g X ≤ conjSub g Y ↔ X ≤ Y
        constructor
        · intro h
          have := conjSub_mono (n := g⁻¹) h
          rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
        · exact conjSub_mono }
  exact e.map_iInf A

omit [Finite G] in
theorem T7A.conjSub_iSup {ι : Sort*} (g : G) (A : ι → Subgroup G) :
    conjSub g (⨆ i, A i) = ⨆ i, conjSub g (A i) := by
  unfold conjSub
  exact Subgroup.map_iSup _ _

omit [Finite G] in
theorem alphaOf_conjSub (g : G) (A : Subgroup G) :
    alphaOf (conjSub g A) = conjSub g (alphaOf A) := by
  have hE : ∀ a : G, conjSub g ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ =
      ⁅oddCoreOf (Subgroup.centralizer ({g * a * g⁻¹} : Set G)), conjSub g A⁆ := by
    intro a
    rw [T7A.oddCoreOf_centralizer_conj]
    exact Subgroup.map_commutator _ _ (MulAut.conj g).toMonoidHom
  have hO : ∀ a : G, conjSub g (oddCoreOf (Subgroup.centralizer ({a} : Set G))) =
      oddCoreOf (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) := fun a =>
    (T7A.oddCoreOf_centralizer_conj g a).symm
  unfold alphaOf
  rw [T7A.conjSub_sup_eq]
  congr 1
  · simp only [T7A.conjSub_iSup]
    apply le_antisymm
    · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
      have ha : g⁻¹ * b * g ∈ A := mem_conjSub_iff.mp hb
      have ha1 : g⁻¹ * b * g ≠ 1 := by
        intro h
        apply hb1
        have := congrArg (fun x => g * x * g⁻¹) h
        simpa [mul_assoc] using this
      have hb_eq : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      have h2 : ⁅oddCoreOf (Subgroup.centralizer ({b} : Set G)), conjSub g A⁆ =
          conjSub g ⁅oddCoreOf (Subgroup.centralizer ({g⁻¹ * b * g} : Set G)), A⁆ := by
        rw [hE (g⁻¹ * b * g), hb_eq]
      rw [h2]
      exact le_iSup_of_le (g⁻¹ * b * g) (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))
    · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      have hb : g * a * g⁻¹ ∈ conjSub g A := conj_mem_conjSub ha
      have hb1 : g * a * g⁻¹ ≠ 1 := by
        intro h
        apply ha1
        have := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using this
      rw [hE a]
      exact le_iSup_of_le (g * a * g⁻¹) (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))
  · simp only [T7A.conjSub_iInf]
    apply le_antisymm
    · refine le_iInf fun a => le_iInf fun ha => le_iInf fun ha1 => ?_
      have hb : g * a * g⁻¹ ∈ conjSub g A := conj_mem_conjSub ha
      have hb1 : g * a * g⁻¹ ≠ 1 := by
        intro h
        apply ha1
        have := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using this
      rw [hO a]
      exact iInf_le_of_le (g * a * g⁻¹) (iInf_le_of_le hb (iInf_le_of_le hb1 le_rfl))
    · refine le_iInf fun b => le_iInf fun hb => le_iInf fun hb1 => ?_
      have ha : g⁻¹ * b * g ∈ A := mem_conjSub_iff.mp hb
      have ha1 : g⁻¹ * b * g ≠ 1 := by
        intro h
        apply hb1
        have := congrArg (fun x => g * x * g⁻¹) h
        simpa [mul_assoc] using this
      have hb_eq : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      have h2 : conjSub g (oddCoreOf (Subgroup.centralizer ({g⁻¹ * b * g} : Set G))) =
          oddCoreOf (Subgroup.centralizer ({b} : Set G)) := by
        rw [hO (g⁻¹ * b * g), hb_eq]
      rw [← h2]
      exact iInf_le_of_le (g⁻¹ * b * g) (iInf_le_of_le ha (iInf_le_of_le ha1 le_rfl))


theorem Hyp21.conj {K K' J W : Subgroup G} {z u t : G} (h : Hyp21 p f Ω K K' z u J t W)
    (g : G) :
    Hyp21 p f Ω (conjSub g K) (conjSub g K') (g * z * g⁻¹) (g * u * g⁻¹) (conjSub g J)
      (g * t * g⁻¹) (conjSub g W) := by
  have hΩc : ConjInvariant Ω := h.std.stand.hyp.conjInvariant
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b hab => by
    simpa using hab
  refine
    { std :=
        { stand := h.std.stand.of_mem (hΩc g K h.std.stand.mem)
          disconnected := h.std.disconnected
          hz := h.std.hz.conj g
          hK' := twinSet_conj hΩc h.std.hK' g
          hne := fun e => h.std.hne (conjSub_injective g e)
          cex := h.std.cex }
      hu := ?_
      hu2 := ?_
      hu1 := ?_
      huz := fun e => h.huz (hinj _ _ e)
      hJ := ?_
      ht := h.ht.conj g
      htu := ?_
      hW := WSet.conj hΩc h.hW g
      hzW := conj_mem_conjSub h.hzW
      htW := conj_mem_conjSub h.htW }
  · have := conj_mem_conjSub (n := g) h.hu
    rwa [T7A.conjSub_sup_eq] at this
  · calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [h.hu2]; group
  · intro e
    apply h.hu1
    have := congrArg (fun x => g⁻¹ * x * g) e
    simpa [mul_assoc] using this
  · refine ⟨hΩc g J h.hJ.1, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩc hL g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have := omegaNbr_conj hΩc (h.hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  · calc (g * t * g⁻¹) * (g * u * g⁻¹) = g * (t * u) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [h.htu]
      _ = (g * u * g⁻¹) * (g * t * g⁻¹) := by group

end CFSG.ClassicalInvolution.Asc77

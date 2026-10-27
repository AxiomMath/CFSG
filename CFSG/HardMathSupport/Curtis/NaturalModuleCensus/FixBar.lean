module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.AGLEmbedding.ParabAutIrr (map_perfectJoin_le)
open scoped commutatorElement

structure FixBarData {X : Type*} [Group X] [Finite X] (J : Subgroup X) (p : ℕ)
    (v : X) : Prop where
  parab : ∃ T : Subgroup X, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set X) ≤ J ∧
    J ≠ Subgroup.normalizer (T : Set X)
  ne_top : J ≠ ⊤
  cyc : CycPerfect p J
  pow : v ^ p = 1
  ne_one : v ≠ 1
  join : v ∈ perfectJoin J
  fix : ∀ V : Subgroup X, V ≤ Subgroup.centralizer ({v} : Set X) → ⁅V, V⁆ = V → V ≤ J

theorem isSylowTwoOf_top_of_sylow' {Y : Type*} [Group Y] [Finite Y] (P : Sylow 2 Y) :
    IsSylowTwoOf (P : Subgroup Y) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup Y).subgroupOf ⊤).index = (P : Subgroup Y).index from
    Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

section Central

variable {G X : Type*} [Group G] [Group X]

theorem commutator_commutator_eq_one_of_central {a b l : G}
    (ha : ⁅a, l⁆ ∈ Subgroup.center G) (hb : ⁅b, l⁆ ∈ Subgroup.center G) :
    ⁅⁅a, b⁆, l⁆ = 1 := by
  set z₁ : G := ⁅a, l⁆ with hz₁
  set z₂ : G := ⁅b, l⁆ with hz₂
  have c₁ := Subgroup.mem_center_iff.1 ha
  have c₂ := Subgroup.mem_center_iff.1 hb
  have e₁ : a * l * a⁻¹ = z₁ * l := by simp [hz₁, commutatorElement_def, mul_assoc]
  have e₂ : b * l * b⁻¹ = z₂ * l := by simp [hz₂, commutatorElement_def, mul_assoc]
  have e₁' : a⁻¹ * l * a = z₁⁻¹ * l := by
    have h : a⁻¹ * (z₁ * l) * a = l := by rw [← e₁]; group
    have h2 : a⁻¹ * (z₁ * l) * a = z₁ * (a⁻¹ * l * a) := by
      have := c₁ a⁻¹
      calc a⁻¹ * (z₁ * l) * a = (a⁻¹ * z₁) * l * a := by group
        _ = (z₁ * a⁻¹) * l * a := by rw [this]
        _ = z₁ * (a⁻¹ * l * a) := by group
    have h3 : a⁻¹ * l * a = z₁⁻¹ * l := by
      have : z₁ * (a⁻¹ * l * a) = l := h2 ▸ h
      calc a⁻¹ * l * a = z₁⁻¹ * (z₁ * (a⁻¹ * l * a)) := by group
        _ = z₁⁻¹ * l := by rw [this]
    exact h3
  have e₂' : b⁻¹ * l * b = z₂⁻¹ * l := by
    have h : b⁻¹ * (z₂ * l) * b = l := by rw [← e₂]; group
    have h2 : b⁻¹ * (z₂ * l) * b = z₂ * (b⁻¹ * l * b) := by
      have := c₂ b⁻¹
      calc b⁻¹ * (z₂ * l) * b = (b⁻¹ * z₂) * l * b := by group
        _ = (z₂ * b⁻¹) * l * b := by rw [this]
        _ = z₂ * (b⁻¹ * l * b) := by group
    have h3 : b⁻¹ * l * b = z₂⁻¹ * l := by
      have : z₂ * (b⁻¹ * l * b) = l := h2 ▸ h
      calc b⁻¹ * l * b = z₂⁻¹ * (z₂ * (b⁻¹ * l * b)) := by group
        _ = z₂⁻¹ * l := by rw [this]
    exact h3
  have hz₁c : ∀ g : G, g * z₁ = z₁ * g := c₁
  have hz₂c : ∀ g : G, g * z₂ = z₂ * g := c₂
  have key : (a * b * a⁻¹ * b⁻¹) * l * (a * b * a⁻¹ * b⁻¹)⁻¹ = l := by
    have s1 : b⁻¹ * l * b = z₂⁻¹ * l := e₂'
    have s2 : a⁻¹ * (z₂⁻¹ * l) * a = z₂⁻¹ * (z₁⁻¹ * l) := by
      have hc : a⁻¹ * z₂⁻¹ = z₂⁻¹ * a⁻¹ :=
        (Commute.inv_right (show Commute a⁻¹ z₂ from hz₂c a⁻¹)).eq
      calc a⁻¹ * (z₂⁻¹ * l) * a = (a⁻¹ * z₂⁻¹) * l * a := by group
        _ = (z₂⁻¹ * a⁻¹) * l * a := by rw [hc]
        _ = z₂⁻¹ * (a⁻¹ * l * a) := by group
        _ = z₂⁻¹ * (z₁⁻¹ * l) := by rw [e₁']
    have s3 : b * (z₂⁻¹ * (z₁⁻¹ * l)) * b⁻¹ = z₁⁻¹ * l := by
      have hc2 : b * z₂⁻¹ = z₂⁻¹ * b := by
        have := hz₂c b
        calc b * z₂⁻¹ = z₂⁻¹ * (z₂ * b) * z₂⁻¹ := by group
          _ = z₂⁻¹ * (b * z₂) * z₂⁻¹ := by rw [← this]
          _ = z₂⁻¹ * b := by group
      have hc1 : b * z₁⁻¹ = z₁⁻¹ * b := by
        have := hz₁c b
        calc b * z₁⁻¹ = z₁⁻¹ * (z₁ * b) * z₁⁻¹ := by group
          _ = z₁⁻¹ * (b * z₁) * z₁⁻¹ := by rw [← this]
          _ = z₁⁻¹ * b := by group
      calc b * (z₂⁻¹ * (z₁⁻¹ * l)) * b⁻¹
          = (b * z₂⁻¹) * (z₁⁻¹ * l) * b⁻¹ := by group
        _ = (z₂⁻¹ * b) * (z₁⁻¹ * l) * b⁻¹ := by rw [hc2]
        _ = z₂⁻¹ * ((b * z₁⁻¹) * l * b⁻¹) := by group
        _ = z₂⁻¹ * ((z₁⁻¹ * b) * l * b⁻¹) := by rw [hc1]
        _ = z₂⁻¹ * z₁⁻¹ * (b * l * b⁻¹) := by group
        _ = z₂⁻¹ * z₁⁻¹ * (z₂ * l) := by rw [e₂]
        _ = z₁⁻¹ * (z₂⁻¹ * z₂) * l := by
          have hz : z₂⁻¹ * z₁⁻¹ = z₁⁻¹ * z₂⁻¹ := by
            have := hz₂c z₁⁻¹
            calc z₂⁻¹ * z₁⁻¹ = z₂⁻¹ * z₁⁻¹ := rfl
              _ = z₂⁻¹ * (z₁⁻¹ * z₂) * z₂⁻¹ := by group
              _ = z₂⁻¹ * (z₂ * z₁⁻¹) * z₂⁻¹ := by rw [this]
              _ = z₁⁻¹ * z₂⁻¹ := by group
          calc z₂⁻¹ * z₁⁻¹ * (z₂ * l) = (z₂⁻¹ * z₁⁻¹) * z₂ * l := by group
            _ = (z₁⁻¹ * z₂⁻¹) * z₂ * l := by rw [hz]
            _ = z₁⁻¹ * (z₂⁻¹ * z₂) * l := by group
        _ = z₁⁻¹ * l := by group
    have s4 : a * (z₁⁻¹ * l) * a⁻¹ = l := by
      have hc : a * z₁⁻¹ = z₁⁻¹ * a := by
        have := hz₁c a
        calc a * z₁⁻¹ = z₁⁻¹ * (z₁ * a) * z₁⁻¹ := by group
          _ = z₁⁻¹ * (a * z₁) * z₁⁻¹ := by rw [← this]
          _ = z₁⁻¹ * a := by group
      calc a * (z₁⁻¹ * l) * a⁻¹ = (a * z₁⁻¹) * l * a⁻¹ := by group
        _ = (z₁⁻¹ * a) * l * a⁻¹ := by rw [hc]
        _ = z₁⁻¹ * (a * l * a⁻¹) := by group
        _ = z₁⁻¹ * (z₁ * l) := by rw [e₁]
        _ = l := by group
    calc (a * b * a⁻¹ * b⁻¹) * l * (a * b * a⁻¹ * b⁻¹)⁻¹
        = a * (b * (a⁻¹ * (b⁻¹ * l * b) * a) * b⁻¹) * a⁻¹ := by group
      _ = a * (b * (a⁻¹ * (z₂⁻¹ * l) * a) * b⁻¹) * a⁻¹ := by rw [s1]
      _ = a * (b * (z₂⁻¹ * (z₁⁻¹ * l)) * b⁻¹) * a⁻¹ := by rw [s2]
      _ = a * (z₁⁻¹ * l) * a⁻¹ := by rw [s3]
      _ = l := s4
  have : ⁅⁅a, b⁆, l⁆ = (a * b * a⁻¹ * b⁻¹) * l * (a * b * a⁻¹ * b⁻¹)⁻¹ * l⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [this, key]
  group

end Central

section Quotient

variable {G X : Type*} [Group G] [Finite G] [Group X] {ψ : G →* X}

theorem exists_pSubgroup_map_eq {p : ℕ} (hp : p.Prime) {P : Subgroup G} {Q : Subgroup X}
    (hP : P.map ψ = Q) (hQ : IsPGroup p Q) :
    ∃ R : Subgroup G, R ≤ P ∧ IsPGroup p R ∧ R.map ψ = Q := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ x : ↥P, ψ x ∈ Q := fun x => hP ▸ ⟨x, x.2, rfl⟩
  let ψ' : ↥P →* ↥Q := (ψ.comp P.subtype).codRestrict Q hmem
  have hψ' : Function.Surjective ψ' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := (hP ▸ hy : y ∈ P.map ψ)
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨S⟩ : Nonempty (Sylow p ↥P) := inferInstance
  let S' : Sylow p ↥Q := S.mapSurjective hψ'
  have htop : (⊤ : Subgroup ↥Q) = (S' : Subgroup ↥Q) :=
    S'.is_maximal' (IsPGroup.of_equiv (hQ) Subgroup.topEquiv.symm) le_top
  refine ⟨(S : Subgroup ↥P).map P.subtype, ?_, S.isPGroup'.map P.subtype, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact hmem x
    · intro y hy
      have hy' : (⟨y, hy⟩ : ↥Q) ∈ (S' : Subgroup ↥Q) := htop ▸ Subgroup.mem_top _
      rw [Sylow.coe_mapSurjective] at hy'
      obtain ⟨x, hx, hxy⟩ := hy'
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩

theorem fixBarData_of_central_quotient [Finite X] (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card ψ.ker))
    {J : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hpar : ∃ T : Subgroup G, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set G) ≤ J ∧
      J ≠ Subgroup.normalizer (T : Set G))
    (htop : J ≠ ⊤) (hcyc : CycPerfect p J) {l : G} (hlp : l ^ p ∈ ψ.ker) (hl : l ∉ ψ.ker)
    (hlj : l ∈ perfectJoin J) (hfix : ∀ g : G, g * l = l * g → g ∈ J) :
    FixBarData (J.map ψ) p (ψ l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ, hneB⟩ := hpar
  have hkJ : ψ.ker ≤ J :=
    hker.trans ((Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)).trans hNJ)
  have hcomap : (J.map ψ).comap ψ = J := Subgroup.comap_map_eq_self hkJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hidx : ¬ 2 ∣ T.index := by
      have h := hT.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
    let T' : Sylow 2 G := hT.2.1.toSylow hidx
    refine ⟨T.map ψ, ?_, ?_, ?_⟩
    · have := isSylowTwoOf_top_of_sylow' (T'.mapSurjective hψ)
      rwa [show ((T'.mapSurjective hψ : Sylow 2 X) : Subgroup X) = T.map ψ from
        Sylow.coe_mapSurjective hψ T'] at this
    · exact ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1 hNJ
    · intro hJe
      apply hneB
      refine le_antisymm (fun x hx => ?_) hNJ
      have hmem : ψ x ∈ Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := by
        rw [← hJe]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hyN, hyx⟩ := ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1
        (le_refl (Subgroup.normalizer (T : Set G))) hmem
      have hxy : y⁻¹ * x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hzN : y⁻¹ * x ∈ Subgroup.normalizer (T : Set G) :=
        (Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)) (hker hxy)
      simpa using Subgroup.mul_mem _ hyN hzN
  · intro h
    apply htop
    rw [← hcomap, h, Subgroup.comap_top]
  ·
    intro V hVJ hV Q hQV hQp
    obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
      (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
    have hWJ : W ≤ J := by
      refine hWle.trans ?_
      rw [← hcomap]
      exact Subgroup.comap_mono hVJ
    have hPmap : (W ⊓ Q.comap ψ).map ψ = Q := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        have hyV : y ∈ W.map ψ := by rw [hWmap]; exact hQV hy
        obtain ⟨w, hw, rfl⟩ := hyV
        exact ⟨w, ⟨hw, hy⟩, rfl⟩
    obtain ⟨R, hRP, hRp, hRmap⟩ := exists_pSubgroup_map_eq hp hPmap hQp
    have hRW : R ≤ W := fun x hx => (hRP hx).1
    have hRcyc : IsCyclic R := hcyc W hWJ hW R hRW hRp
    subst hRmap
    have := hRcyc
    exact isCyclic_of_surjective (ψ.subgroupMap R) (ψ.subgroupMap_surjective R)
  · rw [← map_pow]
    exact MonoidHom.mem_ker.1 hlp
  · intro h
    exact hl (MonoidHom.mem_ker.2 h)
  · exact map_perfectJoin_le ψ le_rfl ⟨l, hlj, rfl⟩
  ·
    intro V hVC hV
    obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
      (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
    have hcentral : ∀ w ∈ W, ⁅w, l⁆ ∈ Subgroup.center G := by
      intro w hw
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      have hwV : ψ w ∈ V := by rw [← hWmap]; exact ⟨w, hw, rfl⟩
      exact (Subgroup.mem_centralizer_iff.1 (hVC hwV) (ψ l) (Set.mem_singleton _)).symm
    have hWC : W ≤ Subgroup.centralizer ({l} : Set G) := by
      rw [← hW]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := commutator_commutator_eq_one_of_central (hcentral a ha) (hcentral b hb)
      rw [commutatorElement_eq_one_iff_commute] at h1
      exact h1.symm
    have hWJ : W ≤ J := fun w hw =>
      hfix w ((Subgroup.mem_centralizer_iff.1 (hWC hw) l (Set.mem_singleton _)).symm)
    rw [← hWmap]
    exact Subgroup.map_mono hWJ

end Quotient

section Equiv

variable {X X' : Type*} [Group X] [Group X']

theorem map_perfectJoin_mulEquiv (e : X ≃* X') (J : Subgroup X) :
    (perfectJoin J).map e.toMonoidHom = perfectJoin (J.map e.toMonoidHom) := by
  refine le_antisymm (map_perfectJoin_le e.toMonoidHom le_rfl) ?_
  have h := map_perfectJoin_le e.symm.toMonoidHom
    (J := J.map e.toMonoidHom) (J' := J) (by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simpa using hx)
  intro y hy
  have h1 : e.symm.toMonoidHom y ∈ perfectJoin J := h ⟨y, hy, rfl⟩
  exact ⟨e.symm y, h1, by simp⟩

theorem map_map_symm (e : X ≃* X') (K : Subgroup X') :
    (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩

theorem FixBarData.map_mulEquiv [Finite X] [Finite X'] (e : X ≃* X') {J : Subgroup X} {p : ℕ} {v : X}
    (h : FixBarData J p v) : FixBarData (J.map e.toMonoidHom) p (e v) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨T, hT, hNJ, hne⟩ := h.parab
    refine ⟨T.map e.toMonoidHom, ⟨le_top, hT.2.1.map _, ?_⟩, ?_, ?_⟩
    · have h2 := hT.2.2
      have e1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
      have e2 : ((T.map e.toMonoidHom).subgroupOf ⊤).index = (T.map e.toMonoidHom).index :=
        Subgroup.relIndex_top_right _
      rw [e2, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective T]
      rwa [e1] at h2
    · rw [← Subgroup.map_normalizer_eq_of_bijective (T : Subgroup X) e.bijective]
      exact Subgroup.map_mono hNJ
    · intro heq
      apply hne
      rw [← Subgroup.map_normalizer_eq_of_bijective (T : Subgroup X) e.bijective] at heq
      exact Subgroup.map_injective hinj heq
  · intro htop
    apply h.ne_top
    apply Subgroup.map_injective hinj
    rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]
  · intro V hVJ hV Q hQV hQp
    have hV' : V.map e.symm.toMonoidHom ≤ J := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hVJ hy
      simpa using hz
    have hVp : ⁅V.map e.symm.toMonoidHom, V.map e.symm.toMonoidHom⁆ = V.map e.symm.toMonoidHom := by
      rw [← Subgroup.map_commutator, hV]
    have hQ' : Q.map e.symm.toMonoidHom ≤ V.map e.symm.toMonoidHom := Subgroup.map_mono hQV
    have := h.cyc _ hV' hVp _ hQ' (hQp.map _)
    have hQeq := map_map_symm e Q
    rw [← hQeq]
    exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap _)
      (e.toMonoidHom.subgroupMap_surjective _)
  · rw [← map_pow, h.pow, map_one]
  · intro h1
    apply h.ne_one
    exact e.injective (by rw [map_one]; exact h1)
  · rw [← map_perfectJoin_mulEquiv e J]
    exact ⟨v, h.join, rfl⟩
  · intro V hVC hV
    have hVc : V.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({v} : Set X) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have := Subgroup.mem_centralizer_iff.1 (hVC hy) (e g) (by simp)
      apply e.injective
      simpa using this
    have hVp : ⁅V.map e.symm.toMonoidHom, V.map e.symm.toMonoidHom⁆ = V.map e.symm.toMonoidHom := by
      rw [← Subgroup.map_commutator, hV]
    have := h.fix _ hVc hVp
    rw [← map_map_symm e V]
    exact Subgroup.map_mono this

end Equiv

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus

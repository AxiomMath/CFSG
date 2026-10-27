module

public import CFSG.HardMathSupport.Dickson.ElementCaseBp.BpTransport
public import CFSG.HardMathSupport.Dickson.ElementCaseBp.FixedCommutator
public import CFSG.HardMathSupport.Dickson.ElementCaseBp.LayerMap
public import CFSG.HardMathSupport.Dickson.ElementCaseBp.LayerSup

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open scoped commutatorElement

private theorem mem_range_conj_of_mem_sup_centralizer {G : Type*} [Group G] {K : Subgroup G}
    {g : G} (hg : g ∈ K ⊔ Subgroup.centralizer (K : Set G))
    (hgN : g ∈ Subgroup.normalizer (K : Set G)) :
    Subgroup.normalizerMonoidHom K ⟨g, hgN⟩ ∈ (MulAut.conj : K →* MulAut K).range := by
  have hle : K ⊔ Subgroup.centralizer (K : Set G) ≤
      (((MulAut.conj : K →* MulAut K).range).comap (Subgroup.normalizerMonoidHom K)).map
        (Subgroup.normalizer (K : Set G)).subtype := by
    refine sup_le (fun k hk => ?_) (fun t ht => ?_)
    · refine Subgroup.mem_map.mpr
        ⟨⟨k, Subgroup.le_normalizer hk⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      rw [normalizerMonoidHom_of_mem hk]
      exact ⟨_, rfl⟩
    · refine Subgroup.mem_map.mpr ⟨⟨t, Subgroup.centralizer_le_normalizer _ ht⟩,
        Subgroup.mem_comap.mpr ?_, rfl⟩
      rw [(normalizerMonoidHom_eq_one_iff ⟨t, _⟩).mpr ht]
      exact one_mem _
  obtain ⟨s, hs, hsg⟩ := hle hg
  have hsg' : s = ⟨g, hgN⟩ := Subtype.ext hsg
  rw [hsg'] at hs
  exact hs

private theorem range_normal_of_commutator_mem_range {M D : Type*} [Group M] [Group D]
    (ψ : M →* D) (h : ∀ d₁ d₂ : D, ⁅d₁, d₂⁆ ∈ ψ.range) : ψ.range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (h g n) hn

private theorem coe_commutatorElement_subgroup {G : Type*} [Group G] {H : Subgroup G}
    (a b : H) : ((⁅a, b⁆ : H) : G) = ⁅(a : G), (b : G)⁆ := by
  simp [commutatorElement_def]

private theorem commutator_eq_bot_of_three_subgroups {Y : Type*} [Group Y]
    {A₁ A₃ Pl Pc : Subgroup Y} (h1 : A₁ ≤ Pl) (hPP : ⁅Pc, Pl⁆ = ⊥) (h13 : ⁅A₁, A₃⁆ ≤ Pc)
    (hperf : ⁅A₁, A₁⁆ = A₁) : ⁅A₁, A₃⁆ = ⊥ := by
  have e1 : ⁅⁅A₁, A₃⁆, A₁⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono h13 h1).trans hPP.le)
  have e2 : ⁅⁅A₃, A₁⁆, A₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm A₃ A₁]
    exact e1
  have e3 := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := A₁) (H₂ := A₁) (H₃ := A₃) e1 e2
  rwa [hperf] at e3

private theorem commutator_le_ker_of_perfect {N Y : Type*} [Group N] [Group Y] (Φ : N →* Y)
    {L' O' : Subgroup N} {Pl Pc : Subgroup Y} (hperf : ⁅L', L'⁆ = L')
    (h1 : ∀ a ∈ L', Φ a ∈ Pl) (h13 : ∀ a ∈ L', ∀ b ∈ O', Φ ⁅a, b⁆ ∈ Pc)
    (hPP : ⁅Pc, Pl⁆ = ⊥) : ⁅L', O'⁆ ≤ Φ.ker := by
  have hperf' : ⁅L'.map Φ, L'.map Φ⁆ = L'.map Φ := by
    rw [← Subgroup.map_commutator, hperf]
  have hbot : ⁅L'.map Φ, O'.map Φ⁆ = ⊥ := by
    refine commutator_eq_bot_of_three_subgroups (Pl := Pl) (Pc := Pc) ?_ hPP ?_ hperf'
    · rintro _ ⟨a, ha, rfl⟩
      exact h1 a ha
    · refine Subgroup.commutator_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_commutatorElement Φ a b]
      exact h13 a ha b hb
  rw [← Subgroup.map_commutator] at hbot
  exact (Subgroup.map_eq_bot_iff _).mp hbot

private theorem commutator_le_centralizer_of_images {Z : Type*} [Group Z] {K L O : Subgroup Z}
    {Pl Pc : Subgroup (MulAut ↥K)} (hLN : L ≤ Subgroup.normalizer (K : Set Z))
    (hOK : O ≤ Subgroup.normalizer (K : Set Z)) (hLL : ⁅L, L⁆ = L)
    (hA1 : ∀ a : ↥(Subgroup.normalizer (K : Set Z)), (a : Z) ∈ L →
      Subgroup.normalizerMonoidHom K a ∈ Pl)
    (hOD : ∀ a b : ↥(Subgroup.normalizer (K : Set Z)), (a : Z) ∈ L → (b : Z) ∈ O →
      Subgroup.normalizerMonoidHom K ⁅a, b⁆ ∈ Pc)
    (hPP : ⁅Pl, Pc⁆ = ⊥) : ⁅L, O⁆ ≤ Subgroup.centralizer (K : Set Z) := by
  have hperfN : ⁅L.subgroupOf (Subgroup.normalizer (K : Set Z)),
      L.subgroupOf (Subgroup.normalizer (K : Set Z))⁆ =
        L.subgroupOf (Subgroup.normalizer (K : Set Z)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (K : Set Z)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLN, hLL]
  have hker := commutator_le_ker_of_perfect (Subgroup.normalizerMonoidHom K)
    (L' := L.subgroupOf (Subgroup.normalizer (K : Set Z)))
    (O' := O.subgroupOf (Subgroup.normalizer (K : Set Z))) hperfN
    (fun a ha => hA1 a (Subgroup.mem_subgroupOf.mp ha))
    (fun a ha b hb => hOD a b (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))
    (by rw [Subgroup.commutator_comm]; exact hPP)
  refine Subgroup.commutator_le.mpr fun l hl o ho => ?_
  have hlN : l ∈ Subgroup.normalizer (K : Set Z) := hLN hl
  have hoN : o ∈ Subgroup.normalizer (K : Set Z) := hOK ho
  have hmem : (⁅(⟨l, hlN⟩ : ↥(Subgroup.normalizer (K : Set Z))), ⟨o, hoN⟩⁆ :
      ↥(Subgroup.normalizer (K : Set Z))) ∈
      ⁅L.subgroupOf (Subgroup.normalizer (K : Set Z)),
        O.subgroupOf (Subgroup.normalizer (K : Set Z))⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hl)
      (Subgroup.mem_subgroupOf.mpr ho)
  have := (normalizerMonoidHom_eq_one_iff _).mp (MonoidHom.mem_ker.mp (hker hmem))
  rwa [coe_commutatorElement_subgroup] at this

private theorem isPComponent_subgroupOf_of_le {Z : Type*} [Group Z] [Finite Z] {p : ℕ}
    [Fact p.Prime] {L M C : Subgroup Z} (hLM : L ≤ M) (hMC : M ≤ C)
    (hL : CFSG.IsPComponent p (L.subgroupOf C)) : CFSG.IsPComponent p (L.subgroupOf M) := by
  have hLC : L ≤ C := hLM.trans hMC
  obtain ⟨hsub, hres, hqs⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p L C hLC).mp hL
  refine (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p L M
    hLM).mpr ⟨?_, hres, hqs⟩
  have h := Subgroup.IsSubnormal.comap (Subgroup.inclusion hMC) hsub
  have e : (L.subgroupOf C).comap (Subgroup.inclusion hMC) = L.subgroupOf M := by
    ext m
    simp [Subgroup.mem_subgroupOf]
  rwa [e] at h

private theorem commutator_le_centralizer_of_normal_range {Z : Type*} [Group Z] [Finite Z]
    {p : ℕ} [Fact p.Prime] {K C L E : Subgroup Z} [E.Normal] (hLC : L ≤ C)
    (hL : CFSG.IsPComponent p (L.subgroupOf C)) (hLE : L ≤ E)
    (hEN : E ≤ Subgroup.normalizer (K : Set Z))
    (hOK : (CFSG.pPrimeCore p ↥C).map C.subtype ≤ Subgroup.normalizer (K : Set Z))
    {D : Subgroup (MulAut ↥K)} (ψ : ↥(C ⊓ E) →* ↥D)
    (hψ : ∀ (m : Z) (hm : m ∈ C ⊓ E) (hmN : m ∈ Subgroup.normalizer (K : Set Z)),
      (ψ ⟨m, hm⟩ : MulAut ↥K) = Subgroup.normalizerMonoidHom K ⟨m, hmN⟩)
    (hψn : ψ.range.Normal)
    (hBD : ⁅(CFSG.pLayer ↥D p).map D.subtype, (CFSG.pPrimeCore p ↥D).map D.subtype⁆ = ⊥) :
    ⁅L, (CFSG.pPrimeCore p ↥C).map C.subtype⁆ ≤ Subgroup.centralizer (K : Set Z) := by
  have hLM : L ≤ C ⊓ E := le_inf hLC hLE
  have hMC : C ⊓ E ≤ C := inf_le_left
  have hLN : L ≤ Subgroup.normalizer (K : Set Z) := hLE.trans hEN
  have hOC : (CFSG.pPrimeCore p ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hLMcomp : CFSG.IsPComponent p (L.subgroupOf (C ⊓ E)) :=
    isPComponent_subgroupOf_of_le hLM hMC hL
  have hLMlayer : L.subgroupOf (C ⊓ E) ≤ CFSG.pLayer ↥(C ⊓ E) p := le_sSup hLMcomp
  have hA1 : ∀ (a : ↥(Subgroup.normalizer (K : Set Z))), (a : Z) ∈ L →
      Subgroup.normalizerMonoidHom K a ∈ (CFSG.pLayer ↥D p).map D.subtype := by
    intro a ha
    have hlM : (a : Z) ∈ C ⊓ E := hLM ha
    have h1 : ψ ⟨a, hlM⟩ ∈ CFSG.pLayer ↥D p :=
      map_pLayer_le_of_range_normal p ψ hψn
        (Subgroup.mem_map_of_mem ψ (hLMlayer (Subgroup.mem_subgroupOf.mpr ha)))
    exact ⟨ψ ⟨a, hlM⟩, h1, hψ a hlM a.2⟩
  have hOcomm : ⁅L, (CFSG.pPrimeCore p ↥C).map C.subtype⁆ ≤
      (CFSG.pPrimeCore p ↥C).map C.subtype := by
    refine Subgroup.commutator_le.mpr fun l hl o ho => ?_
    obtain ⟨q, hq, rfl⟩ := ho
    have hlC : l ∈ C := hLC hl
    refine ⟨⁅(⟨l, hlC⟩ : ↥C), q⁆, ?_, map_commutatorElement C.subtype _ _⟩
    rw [commutatorElement_def]
    exact mul_mem ((CFSG.pPrimeCore_normal (p := p) (G := ↥C)).conj_mem q hq _) (inv_mem hq)
  have hLOE : ⁅L, (CFSG.pPrimeCore p ↥C).map C.subtype⁆ ≤ E :=
    (Subgroup.commutator_mono hLE le_rfl).trans (Subgroup.commutator_le_left E _)
  have hOD : ∀ (a b : ↥(Subgroup.normalizer (K : Set Z))), (a : Z) ∈ L →
      (b : Z) ∈ (CFSG.pPrimeCore p ↥C).map C.subtype →
      Subgroup.normalizerMonoidHom K ⁅a, b⁆ ∈ (CFSG.pPrimeCore p ↥D).map D.subtype := by
    intro a b ha hb
    have hc : ((⁅a, b⁆ : ↥(Subgroup.normalizer (K : Set Z))) : Z) ∈
        ⁅L, (CFSG.pPrimeCore p ↥C).map C.subtype⁆ := by
      rw [coe_commutatorElement_subgroup]
      exact Subgroup.commutator_mem_commutator ha hb
    have hcO := hOcomm hc
    have hcE := hLOE hc
    have hcC := hOC hcO
    have hcM : ((⁅a, b⁆ : ↥(Subgroup.normalizer (K : Set Z))) : Z) ∈ C ⊓ E := ⟨hcC, hcE⟩
    obtain ⟨q, hq, hqc⟩ := hcO
    have hW : (⟨_, hcM⟩ : ↥(C ⊓ E)) ∈
        (CFSG.pPrimeCore p ↥C).comap (Subgroup.inclusion hMC) := by
      show Subgroup.inclusion hMC ⟨_, hcM⟩ ∈ CFSG.pPrimeCore p ↥C
      have e : Subgroup.inclusion hMC ⟨_, hcM⟩ = q := Subtype.ext hqc.symm
      rw [e]
      exact hq
    have hWle : (CFSG.pPrimeCore p ↥C).comap (Subgroup.inclusion hMC) ≤
        CFSG.pPrimeCore p ↥(C ⊓ E) := by
      have hinj : Function.Injective (Subgroup.inclusion hMC) :=
        Subgroup.inclusion_injective hMC
      refine le_sSup ⟨(CFSG.pPrimeCore_normal (p := p) (G := ↥C)).comap _, ?_⟩
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective _ _ hinj) CFSG.pPrimeCore_coprime_card
    have h1 : ψ ⟨_, hcM⟩ ∈ CFSG.pPrimeCore p ↥D :=
      map_pPrimeCore_le_of_range_normal p ψ hψn (Subgroup.mem_map_of_mem ψ (hWle hW))
    exact ⟨ψ ⟨_, hcM⟩, h1, hψ _ hcM (⁅a, b⁆ : ↥(Subgroup.normalizer (K : Set Z))).2⟩
  have hLL : ⁅L, L⁆ = L := by
    have h := Subgroup.isPerfect_iff.mp
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL)
    have h' := congrArg (Subgroup.map C.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLC] at h'
  exact commutator_le_centralizer_of_images hLN hOK hLL hA1 hOD hBD

private theorem exists_normal_range_hom {Z : Type*} [Group Z] {K E : Subgroup Z} {x : Z}
    (hxK : x ∈ Subgroup.normalizer (K : Set Z)) (hKE : K ≤ E)
    (hEsup : E ≤ K ⊔ Subgroup.centralizer (K : Set Z))
    (ι : (↥K ⧸ Subgroup.center ↥K) →* MulAut ↥K)
    (hι_range : ι.range = (MulAut.conj : ↥K →* MulAut ↥K).range)
    (b : MulAut ↥K) (hb_def : b = Subgroup.normalizerMonoidHom K ⟨x, hxK⟩) :
    ∃ ψ : ↥(Subgroup.centralizer ({x} : Set Z) ⊓ E) →*
        ↥(ι.range ⊓ Subgroup.centralizer ({b} : Set (MulAut ↥K))),
      (∀ (m : Z) (hm : m ∈ Subgroup.centralizer ({x} : Set Z) ⊓ E)
        (hmN : m ∈ Subgroup.normalizer (K : Set Z)),
        (ψ ⟨m, hm⟩ : MulAut ↥K) = Subgroup.normalizerMonoidHom K ⟨m, hmN⟩) ∧
      ψ.range.Normal := by
  have hEN : E ≤ Subgroup.normalizer (K : Set Z) :=
    hEsup.trans (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
  have hMN : Subgroup.centralizer ({x} : Set Z) ⊓ E ≤ Subgroup.normalizer (K : Set Z) :=
    inf_le_right.trans hEN
  have hψ₀D : ∀ m : ↥(Subgroup.centralizer ({x} : Set Z) ⊓ E),
      (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hMN) m ∈
        ι.range ⊓ Subgroup.centralizer ({b} : Set (MulAut ↥K)) := by
    intro m
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hι_range]
      exact mem_range_conj_of_mem_sup_centralizer (hEsup (Subgroup.mem_inf.mp m.2).2) _
    · rw [Subgroup.mem_centralizer_singleton_iff, hb_def, MonoidHom.comp_apply, ← map_mul,
        ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp m.2).1)
  refine ⟨((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hMN)).codRestrict _ hψ₀D,
    fun m hm hmN => rfl, ?_⟩
  refine range_normal_of_commutator_mem_range _ fun d₁ d₂ => ?_
  have hinner : ∀ d : MulAut ↥K, d ∈ ι.range → ∃ k : ↥K, MulAut.conj k = d := by
    intro d hd
    rw [hι_range] at hd
    exact hd
  obtain ⟨k₁, hk₁⟩ := hinner _ (Subgroup.mem_inf.mp d₁.2).1
  obtain ⟨k₂, hk₂⟩ := hinner _ (Subgroup.mem_inf.mp d₂.2).1
  have hc₁ : Commute (MulAut.conj k₁) (Subgroup.normalizerMonoidHom K ⟨x, hxK⟩) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d₁.2).2
    rw [← hk₁, hb_def] at h
    exact h
  have hc₂ : Commute (MulAut.conj k₂) (Subgroup.normalizerMonoidHom K ⟨x, hxK⟩) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d₂.2).2
    rw [← hk₂, hb_def] at h
    exact h
  have hc := commutatorElement_mem_centralizer_of_commute_conj hxK hc₁ hc₂
  have hcK : ((⁅k₁, k₂⁆ : ↥K) : Z) ∈ K := (⁅k₁, k₂⁆ : ↥K).2
  have hcM : ((⁅k₁, k₂⁆ : ↥K) : Z) ∈ Subgroup.centralizer ({x} : Set Z) ⊓ E :=
    ⟨hc, hKE hcK⟩
  refine ⟨⟨_, hcM⟩, ?_⟩
  apply Subtype.ext
  rw [coe_commutatorElement_subgroup d₁ d₂]
  show Subgroup.normalizerMonoidHom K ⟨_, hMN hcM⟩ = ⁅(d₁ : MulAut ↥K), (d₂ : MulAut ↥K)⁆
  have e : (⟨((⁅k₁, k₂⁆ : ↥K) : Z), hcK⟩ : ↥K) = ⁅k₁, k₂⁆ := rfl
  rw [normalizerMonoidHom_of_mem hcK, e, map_commutatorElement, hk₁, hk₂]

theorem commutator_le_centralizer_of_mem_normalizer {Z : Type} [Group Z] [Finite Z] {p : ℕ}
    [Fact p.Prime] {K : Subgroup Z} (hK : CFSG.IsComponent K)
    (hB : CFSG.Yardstones.Md42047359a2a.SimpleBp p (↥K ⧸ Subgroup.center ↥K))
    {x : Z} (hxK : x ∈ Subgroup.normalizer (K : Set Z)) (hxc : x ^ p ∈ Subgroup.center Z)
    {L : Subgroup Z} (hLC : L ≤ Subgroup.centralizer ({x} : Set Z))
    (hL : CFSG.IsPComponent p (L.subgroupOf (Subgroup.centralizer ({x} : Set Z))))
    (hLE : L ≤ CFSG.layer Z)
    (hOK : (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({x} : Set Z))).map
      (Subgroup.centralizer ({x} : Set Z)).subtype ≤ Subgroup.normalizer (K : Set Z)) :
    ⁅L, (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({x} : Set Z))).map
      (Subgroup.centralizer ({x} : Set Z)).subtype⁆ ≤ Subgroup.centralizer (K : Set Z) := by
  have hKE : K ≤ CFSG.layer Z := by
    rw [CFSG.layer.eq_sSup]
    exact le_sSup hK
  have hEsup : CFSG.layer Z ≤ K ⊔ Subgroup.centralizer (K : Set Z) :=
    layer_le_sup_centralizer hK
  have hEN : CFSG.layer Z ≤ Subgroup.normalizer (K : Set Z) :=
    hEsup.trans (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
  haveI : (CFSG.layer Z).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨ι, hι_inj, hι_range, hι_apply⟩ := exists_centerQuotient_mulAut ↥K
  obtain ⟨b, hb_def⟩ : ∃ b : MulAut ↥K, b = Subgroup.normalizerMonoidHom K ⟨x, hxK⟩ :=
    ⟨_, rfl⟩
  have hb : ∀ q : ↥K ⧸ Subgroup.center ↥K, b * ι q * b⁻¹ ∈ ι.range := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hι_apply, mul_conj_mul_inv, ← hι_apply]
    exact ⟨_, rfl⟩
  have hbp : b ^ p = 1 := by
    rw [hb_def, ← map_pow, normalizerMonoidHom_eq_one_iff]
    exact Subgroup.center_le_centralizer _ (by simpa using hxc)
  have hBD := commutator_pLayer_pPrimeCore_eq_bot_of_simpleBp (Fact.out) hB ι hι_inj b hb hbp
  obtain ⟨ψ, hψ, hψn⟩ := exists_normal_range_hom hxK hKE hEsup ι hι_range b hb_def
  exact commutator_le_centralizer_of_normal_range hLC hL hLE hEN hOK ψ hψ hψn hBD

end CFSG.HardMathSupport.Dickson.ElementCaseBp

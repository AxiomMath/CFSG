module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Base
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dii

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.mk_mem_centralizer_of_mem_coreActionKernel {M : Subgroup X} {J : Subgroup ↥M}
    {E : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} [IsSimpleGroup ↥E] (heven : 2 ∣ Nat.card ↥E)
    (hJE : J.map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = E) {x : X} (hxM : x ∈ M)
    (hx : x ∈ coreActionKernel (J.map M.subtype)) :
    (QuotientGroup.mk ⟨x, hxM⟩ : ↥M ⧸ pPrimeCore 2 ↥M) ∈ centralizer (E : Set _) := by
  have hJ'M : J.map M.subtype ≤ M := map_subtype_le J
  have hψE : ∀ x' : ↥(J.map M.subtype),
      QuotientGroup.mk' (pPrimeCore 2 ↥M) (Subgroup.inclusion hJ'M x') ∈ E := by
    rintro ⟨_, y, hy, rfl⟩
    rw [← hJE]
    exact ⟨y, hy, rfl⟩
  set ψ : ↥(J.map M.subtype) →* ↥E :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hJ'M)).codRestrict E hψE
    with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    rw [← hJE] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨⟨(y : X), y, hy, rfl⟩, Subtype.ext rfl⟩
  have hK₀ : (pPrimeCore 2 ↥(J.map M.subtype)).map ψ = ⊥ := by
    have hn : ((pPrimeCore 2 ↥(J.map M.subtype)).map ψ).Normal := (pPrimeCore_normal).map ψ hψs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 ↥(J.map M.subtype)).map ψ)
      with h | h
    · exact h
    · exfalso
      have hodd := pPrimeCore_coprime_card (p := 2) (G := ↥(J.map M.subtype))
      have hdvd : Nat.card ↥((pPrimeCore 2 ↥(J.map M.subtype)).map ψ) ∣
          Nat.card ↥(pPrimeCore 2 ↥(J.map M.subtype)) := Subgroup.card_map_dvd _ _
      rw [h, card_top] at hdvd
      exact Nat.prime_two.coprime_iff_not_dvd.mp hodd (heven.trans hdvd)
  rw [mem_centralizer_iff]
  intro e he
  obtain ⟨x', hx'⟩ := hψs ⟨e, he⟩
  obtain ⟨o, ho, hoeq⟩ := hx.2 x' x'.2
  have ho1 : ψ o = 1 := by
    have : ψ o ∈ (pPrimeCore 2 ↥(J.map M.subtype)).map ψ := ⟨o, ho, rfl⟩
    rwa [hK₀, mem_bot] at this
  have hoM : ((o : ↥(J.map M.subtype)) : X) ∈ M := hJ'M o.2
  have h1 : (QuotientGroup.mk ⟨((o : ↥(J.map M.subtype)) : X), hoM⟩ :
      ↥M ⧸ pPrimeCore 2 ↥M) = 1 := congrArg Subtype.val ho1
  have hoeq' : (⟨((o : ↥(J.map M.subtype)) : X), hoM⟩ : ↥M) =
      (Subgroup.inclusion hJ'M x')⁻¹ * (⟨x, hxM⟩ : ↥M)⁻¹ * Subgroup.inclusion hJ'M x' *
        ⟨x, hxM⟩ := Subtype.ext hoeq
  rw [hoeq', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
  have hex : (QuotientGroup.mk (Subgroup.inclusion hJ'M x') : ↥M ⧸ pPrimeCore 2 ↥M) = e :=
    congrArg Subtype.val hx'
  rw [hex] at h1
  calc e * QuotientGroup.mk ⟨x, hxM⟩ =
        QuotientGroup.mk ⟨x, hxM⟩ * e * (e⁻¹ * (QuotientGroup.mk ⟨x, hxM⟩)⁻¹ * e *
          QuotientGroup.mk ⟨x, hxM⟩) := by group
    _ = QuotientGroup.mk ⟨x, hxM⟩ * e := by rw [h1, mul_one]

theorem EndB.nonempty_bar_equiv {M : Subgroup X} {J : Subgroup ↥M}
    {E : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} [IsSimpleGroup ↥E] (heven : 2 ∣ Nat.card ↥E)
    (hJE : J.map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = E) :
    Nonempty (Bar (J.map M.subtype) ≃* ↥E) := by
  have hJ'M : J.map M.subtype ≤ M := map_subtype_le J
  have hψE : ∀ x' : ↥(J.map M.subtype),
      QuotientGroup.mk' (pPrimeCore 2 ↥M) (Subgroup.inclusion hJ'M x') ∈ E := by
    rintro ⟨_, y, hy, rfl⟩
    rw [← hJE]
    exact ⟨y, hy, rfl⟩
  set ψ : ↥(J.map M.subtype) →* ↥E :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hJ'M)).codRestrict E hψE
    with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    rw [← hJE] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨⟨(y : X), y, hy, rfl⟩, Subtype.ext rfl⟩
  have hψk : ¬ 2 ∣ Nat.card ψ.ker := by
    have hle : ψ.ker.map (Subgroup.inclusion hJ'M) ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x', hx', rfl⟩
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) (Subgroup.inclusion hJ'M x') = 1 :=
        congrArg Subtype.val hx'
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcard : Nat.card ψ.ker = Nat.card ↥(ψ.ker.map (Subgroup.inclusion hJ'M)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJ'M)).symm
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [← hcard] at hdvd
    intro h2
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card (h2.trans hdvd)
  obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective ψ hψs hψk
  have hOE : pPrimeCore 2 ↥E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥E) with h | h
    · exact h
    · exfalso
      have hodd := pPrimeCore_coprime_card (p := 2) (G := ↥E)
      rw [h, card_top] at hodd
      exact Nat.prime_two.coprime_iff_not_dvd.mp hodd heven
  exact ⟨e₁.trans ((QuotientGroup.quotientMulEquivOfEq hOE).trans QuotientGroup.quotientBot)⟩

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem exists_J (hc : L2Ctx hs W) :
    ∃ J : Subgroup ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)),
      IsPComponent 2 J ∧
      J.map (QuotientGroup.mk' (pPrimeCore 2
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) =
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have := hc.simple
  set E := layer (MBar β) with hE
  have hKE := hs.KBar_le_layer
  obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 (hs.lieModel_KBar hc.h412)
  have hEnab : ∃ a b : ↥E, a * b ≠ b * a := ⟨⟨a, hKE a.2⟩, ⟨b, hKE b.2⟩, fun h => hab
    (Subtype.ext (by have := congrArg Subtype.val h; simpa using this))⟩
  have hEq : IsQuasisimple ↥E := HarrisEnd.isQuasisimple_of_isSimpleGroup hEnab
  have hcomp : IsComponent E :=
    ⟨hEq, (@normal_of_characteristic _ _ E LocalCores.layer_characteristic).isSubnormal⟩
  exact LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hcomp

theorem card_W_le (hc : L2Ctx hs W)
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    Nat.card W ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hc.simple
  obtain ⟨J, hJ, hJE⟩ := hc.exists_J
  have heven : 2 ∣ Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    have h1 : 2 ∣ Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
      even_iff_two_dvd.mp (even_card_of_lieModel_psl2 hs.p_ne_two (hs.lieModel_KBar hc.h412))
    refine h1.trans ?_
    rw [← Nat.card_congr (subgroupOfEquivOfLe hs.KBar_le_layer).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨eBar⟩ := EndB.nonempty_bar_equiv heven hJE
  have hr3 : 3 ≤ p ^ (f / 2) := le_trans (hs.prime_p.two_le.lt_of_ne (Ne.symm hs.p_ne_two))
    (Nat.le_self_pow (by have := hs.one_le_half; omega) p)
  have hcfg : Config (w ^ (orderOf w / 2) * t ^ i * z ^ j)
      (J.map (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype) p
      (2 * (f / 2)) :=
    { orderOf_eq := hs.setup.orderOf_beta i j
      le_centralizer := map_subtype_le J
      isPComponent := by
        rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
          (Subgroup.subtype_injective _)]
        exact hJ
      prime := hs.prime_p
      ne_two := hs.p_ne_two
      one_le := by have := hs.one_le_half; omega
      five_le := by
        rw [pow_mul']
        nlinarith
      lieModel := GSThmB.OddQuot.lieModel_of_equiv eBar.symm hc.lie
      isCyclic := fun P => by
        have hmem : ∀ x : ↥(P : Subgroup ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
            Set X) ⊓ coreActionKernel (J.map (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
              Set X)).subtype))),
            (QuotientGroup.mk ⟨((x : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
              Set X) ⊓ coreActionKernel (J.map (centralizer ({w ^ (orderOf w / 2) * t ^ i *
                z ^ j} : Set X)).subtype))) : X), (x : ↥(centralizer ({w ^ (orderOf w / 2) *
                  t ^ i * z ^ j} : Set X) ⊓ coreActionKernel (J.map (centralizer
                    ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype))).2.1⟩ :
              MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
              pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := fun x => by
          rw [← hs.centralizer_layer_eq hc.h412]
          exact EndB.mk_mem_centralizer_of_mem_coreActionKernel heven hJE _ x.1.2.2
        refine isCyclic_of_injective ((((QuotientGroup.mk' _).comp (Subgroup.inclusion
          (inf_le_left : centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ⊓
            coreActionKernel (J.map (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
              Set X)).subtype) ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
                Set X)))).comp (P : Subgroup _).subtype).codRestrict _ hmem)
          fun x y hxy => ?_
        have hP' := P.isPGroup'.map (Subgroup.subtype (centralizer ({w ^ (orderOf w / 2) *
          t ^ i * z ^ j} : Set X) ⊓ coreActionKernel (J.map (centralizer
            ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype)))
        have hP'C := (map_subtype_le (P : Subgroup ↥(centralizer ({w ^ (orderOf w / 2) *
          t ^ i * z ^ j} : Set X) ⊓ coreActionKernel (J.map (centralizer
            ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype)))).trans
          (inf_le_left : centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ⊓
            coreActionKernel (J.map (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
              Set X)).subtype) ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
        have h1 := congrArg Subtype.val hxy
        have h2 := mk_injOn hP'C hP' ⟨x, x.2, rfl⟩ ⟨y, y.2, rfl⟩ h1
        exact Subtype.ext (Subtype.ext h2) }
  have h := hs.max_config _ _ _ _ hcfg
  rw [← hc.card_eq] at h
  exact h.trans_eq hs.sylow.card_eq.symm

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit

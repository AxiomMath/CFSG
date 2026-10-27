module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem relIndex_eq [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) :
    (centralizer ({t} : Set X)).relIndex
      (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) = S.relIndex V := by
  have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
  have htM : t ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    Subgroup.le_normalizer htT
  have htV : t ∈ V := hSV (h.t_mem hS)
  have hkM := ncard_conj_orbit _ htM
  have hkV : {y : X | ∃ v ∈ V, v * t * v⁻¹ = y}.ncard = S.relIndex V := by
    rw [ncard_conj_orbit V htV, ← inf_relIndex_right, inf_comm, hσ.inf_centralizer_t hV hSV]
  rw [← hkM, ← hkV]
  congr 1
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨v, hv, hvt⟩ := hσ.exists_conj_V hKF hV hSV hn
    exact ⟨v, hv, hvt⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hV.le hv, rfl⟩

@[expose] def normalizerTAction [Finite X] (hσ : Setup42 h hS w z) :
    ↥(normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) →*
      MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) :=
  (normalizerConj (closure {t, w ^ (orderOf w / 2), z})).comp
    (Subgroup.inclusion hσ.normalizer_T_le_normalizer_X)

theorem normalizerTAction_apply [Finite X] (hσ : Setup42 h hS w z)
    (n : ↥(normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (x : ↥(closure {t, w ^ (orderOf w / 2), z})) :
    ((hσ.normalizerTAction n x : ↥(closure {t, w ^ (orderOf w / 2), z})) : X) =
      (n : X) * x * (n : X)⁻¹ :=
  rfl

theorem mem_ker_normalizerTAction [Finite X] (hσ : Setup42 h hS w z)
    (n : ↥(normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))) :
    n ∈ hσ.normalizerTAction.ker ↔
      (n : X) ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1
    refine mem_centralizer_iff.mpr fun x hx => ?_
    have h2 := congrArg (fun ψ : MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) =>
      ((ψ ⟨x, hx⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) : X)) h1
    simp only [normalizerTAction_apply, MulAut.one_apply] at h2
    calc x * n = ((n : X) * x * (n : X)⁻¹) * n := by rw [h2]
      _ = n * x := by group
  · intro hn
    ext x
    rw [normalizerTAction_apply, MulAut.one_apply]
    have hc := mem_centralizer_iff.mp hn x x.2
    calc (n : X) * x * (n : X)⁻¹ = (x * n) * (n : X)⁻¹ := by rw [hc]
      _ = x := by group

theorem isPGroup_range [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z) :
    IsPGroup 2 hσ.normalizerTAction.range := by
  classical
  obtain ⟨V, hV, hSV⟩ := exists_isSylowOf_ge hS.isPGroup hσ.S_le_normalizer_T
  have hk := hσ.relIndex_eq hKF hV hSV
  set M := normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) with hM
  have hdvd : S.relIndex V ∣ 2 ^ (Nat.card M).factorization 2 := by
    rw [← hV.card_eq]
    exact Subgroup.relIndex_dvd_card (H := S) (K := V)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  set ψ := hσ.normalizerTAction.comp
    (Subgroup.inclusion (inf_le_right : centralizer ({t} : Set X) ⊓ M ≤ M)) with hψ
  have hψ2 : IsPGroup 2 ψ.range := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
    have hx2 := hσ.sq_mem_centralizer_X (Subgroup.mem_inf.mp x.2).2 (Subgroup.mem_inf.mp x.2).1
    have := (hσ.mem_ker_normalizerTAction (Subgroup.inclusion inf_le_right (x ^ 2))).mpr
      (by simpa using hx2)
    exact this
  obtain ⟨f', hf'⟩ := IsPGroup.iff_card.mp hψ2
  have hkerφ : Nat.card hσ.normalizerTAction.ker = Nat.card
      (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) ⊓ M :
        Subgroup X) := by
    have : hσ.normalizerTAction.ker =
        (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X)).subgroupOf M :=
      by
        ext n
        rw [hσ.mem_ker_normalizerTAction]
        rfl
    rw [this, ← Subgroup.card_map_of_injective M.subtype_injective, subgroupOf_map_subtype]
  have hkerψ : Nat.card ψ.ker = Nat.card
      (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) ⊓ M :
        Subgroup X) := by
    have hCXt : centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) ≤
        centralizer ({t} : Set X) := centralizer_le (by
          rw [Set.singleton_subset_iff]
          exact subset_closure (by simp))
    have : ψ.ker = (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) :
        Set X)).subgroupOf (centralizer ({t} : Set X) ⊓ M) := by
      ext x
      rw [hψ, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
        hσ.mem_ker_normalizerTAction]
      rfl
    rw [this, ← Subgroup.card_map_of_injective (centralizer ({t} : Set X) ⊓ M).subtype_injective,
      subgroupOf_map_subtype, ← inf_assoc, inf_of_le_left hCXt]
  have h1 := Subgroup.card_ker_mul_card_range hσ.normalizerTAction
  have h2 := Subgroup.card_ker_mul_card_range ψ
  have h3 := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set X)) (K := M)
  rw [hkerφ] at h1
  rw [hkerψ, hf'] at h2
  rw [hk, he] at h3
  have hpos : 0 < Nat.card
      (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) ⊓ M :
        Subgroup X) := Nat.card_pos
  have hrange : Nat.card hσ.normalizerTAction.range = 2 ^ (e + f') := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, ← h3, ← h2, pow_add]
    ring
  exact IsPGroup.of_card hrange

theorem exists_conj_W [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {F : Subgroup X} (hTF : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ F) {W : Subgroup X}
    (hW : IsSylowOf 2 W
      (F ⊓ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    {g : X} (hg : g ∈ F) (hgX : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) :
    ∃ v ∈ W, v * t * v⁻¹ = g * t * g⁻¹ := by
  classical
  obtain ⟨n, hnF, hnN, hnt⟩ := hσ.exists_normalizer_conj_eq hTF hg hgX
  set M := normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) with hM
  set ψ := hσ.normalizerTAction.comp (Subgroup.inclusion (inf_le_right : F ⊓ M ≤ M)) with hψ
  have hψ2 : IsPGroup 2 ψ.range := by
    have hle : ψ.range ≤ hσ.normalizerTAction.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    exact (hσ.isPGroup_range hKF).to_le hle
  obtain ⟨Q, hQ⟩ := hW.exists_sylow_eq_subgroupOf
  obtain ⟨x, hxQ, hx⟩ := exists_eq_of_isPGroup_range ψ hψ2 Q ⟨n, hnF, hnN⟩
  rw [hQ] at hxQ
  refine ⟨x, hxQ, ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) =>
    ((φ ⟨t, subset_closure (by simp)⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) : X)) hx
  simp only [hψ, MonoidHom.comp_apply, normalizerTAction_apply] at h1
  rw [← hnt]
  exact h1.symm

theorem exists_conj_V_of_mem_X [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    {g : X} (hgX : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) :
    ∃ v ∈ V, v * t * v⁻¹ = g * t * g⁻¹ := by
  have hV' : IsSylowOf 2 V
      (⊤ ⊓ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) := by
    rwa [top_inf_eq]
  exact hσ.exists_conj_W hKF le_top hV' (mem_top g) hgX

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit

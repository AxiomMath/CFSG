module

public import CFSG.Quasithin.H13.L32A753j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A753a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

namespace Ctx753

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem not_two_factor_F4
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38_F4)
    {J : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))}
    (hKJ : autIH (fsuV1 T V) V (hz T V) K ≤ stabSub J)
    (hC₀J : fixV (autIH (fsuV1 T V) V (hz T V) K) ≤ J)
    (hirr : M753.IrrBetween (autIH (fsuV1 T V) V (hz T V) K)
      (fixV (autIH (fsuV1 T V) V (hz T V) K)) J)
    (hnt₁ : ∃ k ∈ autIH (fsuV1 T V) V (hz T V) K, ∃ j ∈ J,
      k j * j⁻¹ ∉ fixV (autIH (fsuV1 T V) V (hz T V) K))
    (hnt₂ : ∃ k ∈ autIH (fsuV1 T V) V (hz T V) K,
      ∃ v ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))), k v * v⁻¹ ∉ J)
    (h64₁ : Nat.card (Sec J (fixV (autIH (fsuV1 T V) V (hz T V) K))) = 2 ^ 6)
    (hnat₁ : G2NaturalDerived (autSec (autIH (fsuV1 T V) V (hz T V) K) J
      (fixV (autIH (fsuV1 T V) V (hz T V) K))) ⊤ ⊥ 1)
    (h64₂ : Nat.card (Sec ⊤ J) = 2 ^ 6)
    (hnat₂ : G2NaturalDerived (autSec (autIH (fsuV1 T V) V (hz T V) K) ⊤ J) ⊤ ⊥ 1) : False := by
  obtain ⟨γ, γ', g, x₀, N⟩ := C.exists_not1471_F4 h38
  have s := N.setup
  obtain ⟨-, hQ, h2⟩ := C.hF98.lemma_14_5_18_two s N.le
  obtain ⟨⟨hA2, hr⟩, -⟩ := hQ
  have hsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))), v ^ 2 = 1 := fun v => by
    have h := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V)))).2
      v.1 v.2
    exact Subtype.ext (by simpa using h)
  have hidx := B45Alt.index_le_sq_of_rAV_le_two hsq hA2 hr
  obtain ⟨hfix, h8, b, hbB, -, h64b⟩ := M753.two_factor C.autK_le_autH C.autH_le_normalizer
    C.autH_inf_centralizer_le C.b42TypeU33_autK hKJ hC₀J hirr hnt₁ hnt₂ h64₁ hnat₁ h64₂ hnat₂
    hA2.1 hA2.2.1 hA2.2.2 hidx
  have hUγH := C.hF98.Uγ_le_H s
  have hcardB := C.card_autOn_Uγ s
  have hfixB := C.index_fixV_autOn hUγH
  have hm2 : 2 * mIdx (F8.Uγ V (hz T V) (g : G)) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) =
      mIdx (conjClosure V (hz T V)) (centralizerMod (fsuV1 T V) (conjClosure V (hz T V))
        (F8.Uγ V (hz T V) (g : G))) := by
    show _ = padicValNat 2 _
    rw [← hfixB, hfix, hcardB, ← pow_mul, padicValNat.prime_pow, mul_comm]
  obtain ⟨hmeq, -, hcomm, hA₁, -, -⟩ := h2 hm2
  have hUN : conjClosure V (hz T V) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    C.f918.toHypF98.toHypF91.conjClosure_Vp_le_pCoreOf.trans
      ((pCoreOf_le 2 _).trans C.f918.H_le_normalizer_V₁)
  set D' := ((F8.DH V (fsuV1 T V) (hz T V) (g : G)).subgroupOf (conjClosure V (hz T V))).map
    (tildeHom hUN) with hD'
  set A' := ((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure V (hz T V))).map
    (tildeHom hUN) with hA'

  have hD'idx : D'.index ≤ 8 := by
    have h1 := Subgroup.index_map_dvd
      (H := (F8.DH V (fsuV1 T V) (hz T V) (g : G)).subgroupOf (conjClosure V (hz T V)))
      (tildeHom_surjective hUN)
    have h3 : ((F8.DH V (fsuV1 T V) (hz T V) (g : G)).subgroupOf
        (conjClosure V (hz T V))).index = 8 := by
      show (F8.DH V (fsuV1 T V) (hz T V) (g : G)).relIndex (conjClosure V (hz T V)) = 8
      rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian C.hF98.F911_3), ← hmeq,
        ← hcardB, h8]
    rw [h3] at h1
    exact Nat.le_of_dvd (by norm_num) h1

  have hA'card : Nat.card A' ≤ 2 := by
    have h1 : Nat.card A' ≤
        Nat.card ((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure V (hz T V))) :=
      Nat.card_le_card_of_surjective
        (fun a => (⟨tildeHom hUN a, Subgroup.mem_map_of_mem _ a.2⟩ : A'))
        (by rintro ⟨_, ⟨a, ha, rfl⟩⟩; exact ⟨⟨a, ha⟩, rfl⟩)
    have h2 : Nat.card ((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure V (hz T V))) ≤
        Nat.card (F8.A₁ (fsuV1 T V) (g : G)) :=
      Nat.card_le_card_of_injective
        (fun a => (⟨a.1.1, Subgroup.mem_subgroupOf.1 a.2⟩ : F8.A₁ (fsuV1 T V) (g : G)))
        (fun a a' h => by
          have h' := congrArg (fun y : ↥(F8.A₁ (fsuV1 T V) (g : G)) => (y : G)) h
          exact Subtype.ext (Subtype.ext h'))
    rw [hA₁] at h2
    exact h1.trans h2

  have hb : ∀ d ∈ D', b d * d⁻¹ ∈ A' := by
    rw [autOn_tilde_eq_map_actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V))
      hUγH] at hbB
    obtain ⟨x, hxU, rfl⟩ := hbB
    rintro _ ⟨d, hd, rfl⟩
    have hc : (x : G) * d * (x : G)⁻¹ * (d : G)⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := by
      have := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hxU)
        (Subgroup.mem_subgroupOf.1 hd))
      rwa [commutatorElement_def] at this
    have hcU : (x : G) * d * (x : G)⁻¹ * (d : G)⁻¹ ∈ conjClosure V (hz T V) :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) x.2) d).mp
        d.2) (inv_mem d.2)
    refine ⟨⟨_, hcU⟩, Subgroup.mem_subgroupOf.2 hc, ?_⟩
    change modMk hUN _ hcU = actH _ _ x (modMk hUN (d : G) d.2) * (modMk hUN (d : G) d.2)⁻¹
    rw [actH_modMk C.f918.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V (hz T V)) x d.2,
      ← modMk_inv hUN d.2, ← modMk_mul hUN]
  have hle := M753.index_fixV_zpowers_le hb
  have h16 : D'.index * Nat.card A' ≤ 8 * 2 := Nat.mul_le_mul hD'idx hA'card
  have := h64b.trans (hle.trans h16)
  norm_num at this

theorem lemma14_7_54_F4
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38_F4) :
    (fixV (autIH (fsuV1 T V) V (hz T V) K) = ⊥ ∧
        G2NaturalDerived (autIH (fsuV1 T V) V (hz T V) K) ⊤ ⊥ 1) ∨
      (Nat.card (fixV (autIH (fsuV1 T V) V (hz T V) K)) = 2 ∧
        Nat.card ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) = 2 ^ 7 ∧
        H13.G2WeylDerived (autIH (fsuV1 T V) V (hz T V) K)) := by
  have hsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))), v ^ 2 = 1 := fun v => by
    have h := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V)))).2
      v.1 v.2
    exact Subtype.ext (by simpa using h)
  have hP := C.b42TypeU33_autK
  have hcomm := C.commV_autK
  rcases M753.structure_fixV hsq hP hcomm C.index_fixV_autK_le with
    ⟨-, -, hnat⟩ | ⟨J, hKJ, hC₀J, -, hirr₁, -, hnt₁, hnt₂, h64₁, hnat₁, h64₂, hnat₂⟩
  · have hKC₀ : autIH (fsuV1 T V) V (hz T V) K ≤ stabSub (fixV (autIH (fsuV1 T V) V (hz T V) K)) :=
      M753.le_stabSub_fixV (X := autIH (fsuV1 T V) V (hz T V) K) Subgroup.le_normalizer
    have hf : autIH (fsuV1 T V) V (hz T V) K ⊓ centSec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) =
        ⊥ := by
      rw [eq_bot_iff]
      rintro k ⟨hk, -, hkc⟩
      rw [Subgroup.mem_bot]
      have hnt : ∃ k ∈ autIH (fsuV1 T V) V (hz T V) K, ∃ j ∈ (⊤ : Subgroup _),
          k j * j⁻¹ ∉ fixV (autIH (fsuV1 T V) V (hz T V) K) := by
        by_contra h
        push Not at h
        have htop := M753.trivial_of_le hP h
        apply absurd (B42U33.card_of_b42TypeU33 hP)
        have hK1 : autIH (fsuV1 T V) V (hz T V) K = ⊥ := by
          rw [eq_bot_iff]
          intro k' hk'
          rw [Subgroup.mem_bot]
          exact MulEquiv.ext fun v => htop (Subgroup.mem_top v) k' hk'
        rw [hK1, Subgroup.card_bot]
        norm_num
      have hinj := M753.secHom_injective (le_stabSub_top _) hKC₀
        (M753.isSimpleGroup_of_b42 hP) hnt
      have h1 : M753.secHom (le_stabSub_top _) hKC₀ ⟨k, hk⟩ = 1 :=
        (M753.secHom_eq_one_iff _ _ _).2 fun j _ => hkc j (Subgroup.mem_top j)
      exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))
    have hnat' := InternalSec.g2NaturalDerived_of_autSec hKC₀ hf hnat
    rcases H13.VolI.g2NaturalCover_holds _ hsq _ _ le_rfl hcomm hnat' with h0 | h2
    · exact Or.inl ⟨h0, h0 ▸ hnat'⟩
    · exact Or.inr h2
  · exact (C.not_two_factor_F4 h38 hKJ hC₀J.le hirr₁ hnt₁ hnt₂ h64₁ hnat₁ h64₂ hnat₂).elim

end Ctx753

end CFSG.Quasithin.H13.L32A

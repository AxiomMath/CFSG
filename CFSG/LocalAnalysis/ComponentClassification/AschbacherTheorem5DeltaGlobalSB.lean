module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSBRoot
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalFusion

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_partner (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    {U₁ V₁ : Subgroup G}
    (hU₁N : U₁ ≤ Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔
      AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
          Set G))
    (hU₁H : U₁ ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g = ⊥)
    (hV₁H : V₁ ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hV₁N : V₁ ≤ Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔
      AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
          Set G))
    (hV₁D : V₁ ⊓ Subgroup.normalizer (D : Set G) = ⊥)
    (hV₁card : Nat.card V₁ = Nat.card (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    {u₁ : G} (hu₁ : u₁ ∈ U₁) (hu₁1 : u₁ ≠ 1) :
    ∃ v₁ ∈ V₁, rightConjugate (AschbacherTheorem3.omegaOne d.T) u₁ =
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) v₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate A d.g : Set G)) with hVdef
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hV2 : IsPGroup 2 V := d.sylowS.isPGroup.to_le
    ((AschbacherTheorem3.omegaOne_le _).trans inf_le_left)
  have hcomm := UV_comm hC d hT hWab
  have hUNV : U ≤ Subgroup.normalizer (V : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hcomm.is_comm.comm ⟨v, Subgroup.mem_sup_right hv⟩
        ⟨u, Subgroup.mem_sup_left hu⟩))
  have hVNU : V ≤ Subgroup.normalizer (U : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      congrArg Subtype.val (hcomm.is_comm.comm ⟨u, Subgroup.mem_sup_left hu⟩
        ⟨v, Subgroup.mem_sup_right hv⟩))
  have hUV : U ⊓ V = ⊥ := le_bot_iff.mp ((inf_le_inf_left U
    ((AschbacherTheorem3.omegaOne_le _).trans (inf_le_left.trans d.sylowS.le))).trans
      (EndHyp.U_inf_A hC).le)
  have hK2 : IsPGroup 2 (U ⊔ V : Subgroup G) := IsPGroup.to_sup_of_normal_right' hU2 hV2 hUNV
  have hcardK : Nat.card (U ⊔ V : Subgroup G) = Nat.card U * Nat.card V :=
    card_sup_of_inf_eq_bot hVNU hUV
  have hu₁N := hU₁N hu₁
  have hZK : rightConjugate U u₁ ≤ U ⊔ V := by
    refine (AschbacherTheorem3.rightConjugate_le_rightConjugate (le_sup_left (b := V)) u₁).trans
      (le_of_eq ?_)
    exact (rightConjugate_eq_self_iff _ u₁).mpr hu₁N
  have hgu : d.g * u₁ * d.g⁻¹ ∉ H := fun h => by
    have hmem : u₁ ∈ U₁ ⊓ rightConjugate H d.g := ⟨hu₁, (mem_rightConjugate_iff _ _ _).mpr h⟩
    rw [hU₁H, Subgroup.mem_bot] at hmem
    exact hu₁1 hmem
  have htZ : ∀ x ∈ rightConjugate U u₁, x ≠ 1 → HasType D Abar x (d.g * u₁) := by
    intro x hx _
    have h1 := hasType_conj (hasType_of_mem_conj_factor hC (EndHyp.U_le_L
      ((mem_rightConjugate_iff _ _ _).mp hx))) u₁
    rwa [show u₁⁻¹ * (u₁ * x * u₁⁻¹) * u₁ = x by group] at h1
  have hZX : rightConjugate U u₁ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxZ, hxU⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    apply hgu
    have h1 := hasType_unique hC (twoElt_of_mem hU2 hxU) hx1 (htZ x hxZ hx1)
      (hasType_of_mem_conj_factor hC (EndHyp.U_le_L hxU))
    simpa [mul_assoc] using h1
  obtain ⟨v₁, hv₁, hle⟩ := le_rightConjugate_of_spread hC (K := U ⊔ V) (X := U) (Y := V)
    (Y₁ := V₁) (Z := rightConjugate U u₁) (κX := d.g) (κY := 1) (κZ := d.g * u₁) hK2
    le_sup_left le_sup_right hcardK hcard hV₁N hV₁card
    (fun x hx _ => hasType_of_mem_conj_factor hC (EndHyp.U_le_L hx))
    (fun y hy _ => hasType_of_mem_factor hC (d.sylowS.le
      ((AschbacherTheorem3.omegaOne_le _ hy).1)))
    (fun y₁ hy₁ y₁' hy₁' h => by
      have hmem : y₁ * y₁'⁻¹ ∈ V₁ ⊓ H := ⟨V₁.mul_mem hy₁ (V₁.inv_mem hy₁'), by simpa using h⟩
      rw [hV₁D, Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp hmem)
    (fun y₁ hy₁ h => by
      apply datum_g_not_mem d
      have h1 := (mem_rightConjugate_iff _ _ _).mp (hV₁H hy₁)
      have h2 := H.inv_mem (by simpa using h : y₁ * d.g⁻¹ ∈ H)
      have : d.g = (d.g * y₁ * d.g⁻¹) * (y₁ * d.g⁻¹)⁻¹ := by group
      rw [this]
      exact H.mul_mem h1 (by simpa using h2))
    hZK hZX htZ
  refine ⟨v₁, hv₁, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [rightConjugate_card, rightConjugate_card, hcard]

theorem odd_ncard_sdiff_one {U : Subgroup G} (hU2 : IsPGroup 2 U) (hU : 2 ≤ Nat.card U) :
    Odd ((U : Set G) \ {1}).ncard := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Set.ncard_sdiff_singleton_of_mem (SetLike.mem_coe.mpr U.one_mem), ← Nat.card_coe_set_eq]
  change Odd (Nat.card U - 1)
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  rw [hk] at hU ⊢
  have hk1 : k ≠ 0 := by
    rintro rfl
    simp at hU
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem transitive_U (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hVZ : AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a)
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T)
    (hPnot : ¬ P ≤ Subgroup.normalizer (D : Set G)) {z : G}
    (hzL : z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g)
    (hzP : rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hzK : ¬ rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hnot : ∃ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    {x₀ : G} (hx₀ : x₀ ∈ AschbacherTheorem3.omegaOne d.T) (hx₀1 : x₀ ≠ 1) {x' : G}
    (hx' : x' ∈ AschbacherTheorem3.omegaOne d.T) (hx'1 : x' ≠ 1) :
    ∃ j ∈ Subgroup.normalizer (AschbacherTheorem3.omegaOne d.T : Set G) ⊓
      Subgroup.normalizer (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Set G) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G),
      j⁻¹ * x₀ * j = x' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUZ := le_zStar_conj_of_root hloc hC d hW hT hWab hcard hSH hVZ hP hWP hPH hPT hPnot hzL
    hzP hzK
  obtain ⟨c, -, hcS, hcN, -, hcH, hcC⟩ := exists_root_conj hloc hC d hT hWab hcard hUZ hSH hnot
  obtain ⟨V₁, hV₁H, hV₁N, hV₁D, hV₁card, hV₁2, hV₁U, hV₁q⟩ :=
    exists_L_root hloc hC d hW hT hWab hcard hVZ hP hWP hPH hPT hPnot hzL hzP hzK
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer (L : Set G)) with hVdef
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hV2 : IsPGroup 2 V := d.sylowS.isPGroup.to_le
    ((AschbacherTheorem3.omegaOne_le _).trans inf_le_left)
  have hU4 : 4 ≤ Nat.card U := four_le_card_U hloc hC d
  have hU1 : U ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hU4; omega
  have hV1 : V ≠ ⊥ := fun h => by rw [hcard, h, Subgroup.card_bot] at hU4; omega
  have hcomm := UV_comm hC d hT hWab
  have hUV : U ⊓ V = ⊥ := le_bot_iff.mp ((inf_le_inf_left U
    ((AschbacherTheorem3.omegaOne_le _).trans (inf_le_left.trans d.sylowS.le))).trans
      (EndHyp.U_inf_A hC).le)
  have hcommUV : ∀ x ∈ U, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, Subgroup.mem_sup_left hx⟩
      ⟨y, Subgroup.mem_sup_right hy⟩)
  have hNU : Subgroup.normalizer (U : Set G) ≤ rightConjugate H d.g := normalizer_U_le hC d hUZ hU1
  have hNV : Subgroup.normalizer (V : Set G) ≤ H :=
    normalizer_le_of_le_zStar hC (hVZ.trans (factorZStar_le_zStar hC.hyp a)) hV2 hV1
  have hel₁ := isElemAbelian_rightConjugate (isElemAbelian_omegaOne hT) c
  have htrans : ∀ x ∈ (U : Set G) \ {1}, ∀ y ∈ (U : Set G) \ {1},
      ∃ j ∈ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G),
        j⁻¹ * x * j = y := by
    rintro x ⟨hx, hx1⟩ y ⟨hy, hy1⟩
    obtain ⟨h, hhU, hhV, hhx⟩ := exists_conj_eq_of_spread (U₁ := rightConjugate U c)
      (fun u hu => by rw [← sq]; exact hel₁.2 u hu) hcommUV hUV
      ((Subgroup.one_lt_card_iff_ne_bot V).mpr hV1)
      (by rw [rightConjugate_card, hcard])
      (fun x hx hx1 u hu hux => by
        have hu' : u ∈ rightConjugate U c ⊓ rightConjugate H d.g := by
          refine ⟨hu, centralizer_le_of_mem_zStar_conj hC d.g (hUZ hx) (twoElt_of_mem hU2 hx) hx1
            (Subgroup.mem_centralizer_singleton_iff.mpr ?_)⟩
          calc u * x = u * (u⁻¹ * x * u) := by rw [hux]
            _ = x * u := by group
        rwa [hcH, Subgroup.mem_bot] at hu')
      (fun u hu x hx => root_comm_mem hC d hT hWab hcS hcN hu hx)
      hcC
      (fun u hu hu1 => by
        obtain ⟨v, hv, hsp⟩ := exists_partner hC d hT hWab hcard hcN hcH hV₁H hV₁N hV₁D hV₁card hu
          hu1
        exact ⟨v, hV₁2 v hv, hV₁U v hv, hV₁q v hv, hsp⟩)
      hx (by simpa using hx1) hy (by simpa using hy1)
    refine ⟨h, ⟨?_, ?_⟩, hhx⟩
    · have h1 : h⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
        AschbacherToolkit.mem_normalizer_of_conj_le fun v hv => by simpa using hhU v hv
      simpa using (Subgroup.normalizer (U : Set G)).inv_mem h1
    · have h1 : h⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
        AschbacherToolkit.mem_normalizer_of_conj_le fun v hv => by simpa using hhV v hv
      simpa using (Subgroup.normalizer (V : Set G)).inv_mem h1
  have hNL : ∀ x, x ∈ Subgroup.normalizer (L : Set G) ↔
      d.g * x * d.g⁻¹ ∈ Subgroup.normalizer (A : Set G) := fun x => by
    rw [hLdef, ← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
  have hidx : ∀ j ∈ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G),
      ∀ k ∈ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G),
      j ∉ Subgroup.normalizer (L : Set G) → k ∉ Subgroup.normalizer (L : Set G) →
      j * k ∈ Subgroup.normalizer (L : Set G) := by
    intro j hj k hk hjL hkL
    have hjH : d.g * j * d.g⁻¹ ∈ H := (mem_rightConjugate_iff _ _ _).mp (hNU hj.1)
    have hkH : d.g * k * d.g⁻¹ ∈ H := (mem_rightConjugate_iff _ _ _).mp (hNU hk.1)
    have h := mul_mem_normalizer hC hr hjH hkH (fun h => hjL ((hNL j).mpr h))
      (fun h => hkL ((hNL k).mpr h))
    rw [hNL]
    have e : d.g * (j * k) * d.g⁻¹ = (d.g * j * d.g⁻¹) * (d.g * k * d.g⁻¹) := by group
    rw [e]
    exact h
  have hJΩ : ∀ j ∈ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G),
      ∀ x ∈ (U : Set G) \ {1}, j⁻¹ * x * j ∈ (U : Set G) \ {1} := by
    rintro j ⟨hjU, -⟩ x ⟨hx, hx1⟩
    refine ⟨?_, fun h => hx1 ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (U : Set G)).inv_mem hjU)
        x).mp hx
      simpa using this
    · have h1 : j⁻¹ * x * j = 1 := h
      calc x = j * (j⁻¹ * x * j) * j⁻¹ := by group
        _ = 1 := by rw [h1]; group
  have hodd := odd_ncard_sdiff_one hU2 (by omega)
  obtain ⟨j, hj, hjx⟩ := transitive_inf_of_odd hodd hJΩ htrans hidx ⟨hx₀, hx₀1⟩ ⟨hx', hx'1⟩
  exact ⟨j, hj, hjx⟩

theorem false_of_two_roots (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hLH : ¬ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hVZ : AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a)
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T)
    (hPnot : ¬ P ≤ Subgroup.normalizer (D : Set G)) {z : G}
    (hzL : z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g)
    (hzP : rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hzK : ¬ rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hnot : ∃ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUZ := le_zStar_conj_of_root hloc hC d hW hT hWab hcard hSH hVZ hP hWP hPH hPT hPnot hzL
    hzP hzK
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer (L : Set G)) with hVdef
  set R := P ⊓ H with hRdef
  have hNA : Subgroup.normalizer (A : Set G) ≤ H := factor_normalizer_le D r Abar hC.hyp.hii a
  have hR2 : IsPGroup 2 R := hPH.isPGroup
  have hTR : d.T ≤ R := by
    rw [← hPT]
    exact inf_le_inf_left P hNA
  have hTeq : R ⊓ (H ⊓ Subgroup.normalizer (A : Set G)) = d.T := by
    rw [← hPT, hRdef, inf_assoc, ← inf_assoc H H, inf_idem, inf_eq_right.mpr hNA]
  have hUR : U ≤ R := EndHyp.U_le_T.trans hTR
  have hRN : ¬ R ≤ Subgroup.normalizer (A : Set G) :=
    sylow_not_le_normalizer hC hr a inf_le_right hLH hPH
  have hidx : d.T.relIndex R = 2 := by
    have h1 := card_eq_two_mul hC hr a (inf_le_right : R ≤ H) hRN
    have h2 := Subgroup.relIndex_mul_card d.T R
    have hRA : R ⊓ Subgroup.normalizer (A : Set G) = d.T := by
      rw [← hTeq, ← inf_assoc R H, inf_eq_left.mpr (inf_le_right : R ≤ H)]
    rw [hRA] at h1
    rw [inf_eq_left.mpr hTR, h1] at h2
    have hpos : 0 < Nat.card d.T := Nat.card_pos
    have : d.T.relIndex R * Nat.card d.T = 2 * Nat.card d.T := h2
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hnoinv : ∀ x ∈ R, x ∉ d.T → x ^ 2 ≠ 1 := fun x hx hxT hx2 => hxT (by
    rw [← hPT]
    exact ⟨hx.1, involution_mem_normalizer hloc hC hr (datum_mem_delta d) (hP.le hx.1) hx.2 hx2⟩)
  set Y := L ⊓ H ⊓ Subgroup.centralizer (U : Set G) with hYdef
  have hRY : IsSylowOf 2 R Y := by
    refine hPH.of_le (le_inf (le_inf (inf_le_left.trans hP.le) inf_le_right) ?_) inf_le_left
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h2 : ∃ k : ℕ, (u⁻¹ * x⁻¹ * u * x) ^ (2 ^ k) = 1 :=
      twoElt_of_mem hR2 (R.mul_mem (R.mul_mem (R.mul_mem (R.inv_mem (hUR hu)) (R.inv_mem hx))
        (hUR hu)) hx)
    exact (comm_of_mem_zStar_conj (hP.le hx.1) (hUZ hu) h2).symm
  refine false_of_transitive_fusion hR2 hTR hT hidx hnoinv (four_le_card_U hloc hC d) ?_
  intro u hu hu1 u' hu' hu'1
  obtain ⟨j, ⟨⟨hjU, hjV⟩, hjL⟩, hjx⟩ := transitive_U hloc hC hr d hW hT hWab hcard hSH hVZ hP hWP
    hPH hPT hPnot hzL hzP hzK hnot hu hu1 hu' hu'1
  have hV2 : IsPGroup 2 V := d.sylowS.isPGroup.to_le
    ((AschbacherTheorem3.omegaOne_le _).trans inf_le_left)
  have hV1 : V ≠ ⊥ := by
    intro h
    have hU4 : 4 ≤ Nat.card U := four_le_card_U hloc hC d
    rw [hcard, h, Subgroup.card_bot] at hU4
    omega
  have hjH : j ∈ H :=
    normalizer_le_of_le_zStar hC (hVZ.trans (factorZStar_le_zStar hC.hyp a)) hV2 hV1 hjV
  have hjY : j ∈ Subgroup.normalizer (Y : Set G) := by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hjL, Subgroup.le_normalizer hjH⟩, ?_⟩
    exact AschbacherTheorem3.normalizer_le_normalizer_centralizer U hjU
  obtain ⟨c', hc'Y, hjc'⟩ := exists_mul_mem_normalizer hRY hjY
  have hc'H : c' ∈ H := hc'Y.1.2
  have hc'U : u' * c' = c' * u' := Subgroup.mem_centralizer_iff.mp hc'Y.2 u' hu'
  refine ⟨j * c', ⟨hjc', ?_⟩, ?_⟩
  · rw [← hTeq]
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hjc', ?_⟩
    exact le_normalizer_inf_normalizer hC hr a (H.mul_mem hjH hc'H)
  · calc (j * c')⁻¹ * u * (j * c') = c'⁻¹ * (j⁻¹ * u * j) * c' := by group
      _ = c'⁻¹ * (u' * c') := by rw [hjx, mul_assoc]
      _ = u' := by rw [hc'U]; group

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5

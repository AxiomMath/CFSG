module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaOmega
public import CFSG.LieType.Simplicity.Classical

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier
open SolomonWong (mul_comm_of_sq_eq_one)

theorem isSimpleGroup_K {Q : Type} [Group Q] (D : ToddParabolic Q) : IsSimpleGroup D.K := by
  rcases D.lieModel_K with ⟨-, hK⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hK).2
  all_goals exact absurd h0 (by norm_num)

section G

variable {G : Type} [Group G] {L : Subgroup G}

theorem toddA_comm (D : ToddParabolic L) {a b : G} (ha : a ∈ toddA D) (hb : b ∈ toddA D) :
    a * b = b * a :=
  mul_comm_of_sq_eq_one (toddA_sq D) ha hb

theorem le_toddA_of_isPGroup (D : ToddParabolic L) {R : Subgroup G} (hRL : R ≤ L)
    (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (toddA D : Set G))
    (hRK : ∀ k ∈ toddK D, ∀ r ∈ R, k * r * k⁻¹ ∈ R) : R ≤ toddA D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := R ⊔ toddA D with hM
  have hM2 : IsPGroup 2 M :=
    IsPGroup.to_sup_of_normal_right' hR2 (isPGroup_of_sq (toddA_sq D)) hRN
  have hKM : ∀ k ∈ toddK D, ∀ m ∈ M, k * m * k⁻¹ ∈ M := by
    intro k hk m hm
    have hle : M ≤ M.comap (MulAut.conj k).toMonoidHom :=
      sup_le (fun r hr => mem_sup_left (hRK k hk r hr))
        (fun a ha => mem_sup_right (conj_mem_toddA D hk ha))
    exact hle hm
  set ψ : D.K →* G := L.subtype.comp D.K.subtype with hψ
  set S := M.comap ψ with hS
  have hSn : S.Normal := ⟨fun n hn g => by
    change ψ (g * n * g⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hKM _ ⟨g, g.2, rfl⟩ _ hn⟩
  have := isSimpleGroup_K D
  have hS1 : S = ⊥ := by
    rcases hSn.eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      have hKle : toddK D ≤ M := by
        rintro _ ⟨k, hk, rfl⟩
        have : (⟨k, hk⟩ : D.K) ∈ S := by rw [h1]; exact mem_top _
        exact this
      have : Finite (toddK D) :=
        Nat.finite_of_card_ne_zero (by rw [Setting.card_toddK D]; norm_num)
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hM2.to_le hKle)
      rw [Setting.card_toddK] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  intro r hr
  have hrAK : r ∈ ((toddA D ⊔ toddK D : Subgroup G) : Set G) :=
    Setting.normalizer_inf_L_le D (mem_inf.2 ⟨hRN hr, hRL hr⟩)
  rw [coe_mul_of_right_le_normalizer_left _ _ (Setting.toddK_le_normalizer D)] at hrAK
  obtain ⟨a, ha, _, ⟨k, hk, rfl⟩, hak⟩ := hrAK
  replace hak : a * (k : G) = r := hak
  have hkM : (k : G) ∈ M := by
    have e : (k : G) = a⁻¹ * r := by rw [← hak]; group
    rw [e]
    exact mul_mem (mem_sup_right (inv_mem ha)) (mem_sup_left hr)
  have hkS : (⟨k, hk⟩ : D.K) ∈ S := hkM
  rw [hS1, mem_bot] at hkS
  have hk1 : (k : G) = 1 := by
    have := congrArg (fun x : D.K => ((x : L) : G)) hkS
    simpa using this
  rw [← hak, hk1, mul_one]
  exact ha

theorem conj_conj_eq_of_commutator_mem {D : ToddParabolic L} {q : G}
    (hqA : q ∈ normalizer (toddA D : Set G))
    (hqK : ∀ k ∈ toddK D, q * k * q⁻¹ * k⁻¹ ∈ toddA D) {k a : G} (hk : k ∈ toddK D)
    (ha : a ∈ toddA D) : q * (k * a * k⁻¹) * q⁻¹ = k * (q * a * q⁻¹) * k⁻¹ := by
  have hc : k * (q * a * q⁻¹) * k⁻¹ ∈ toddA D :=
    conj_mem_toddA D hk ((mem_normalizer_iff.1 hqA a).1 ha)
  have e : q * (k * a * k⁻¹) * q⁻¹ = (q * k * q⁻¹ * k⁻¹) * (k * (q * a * q⁻¹) * k⁻¹) *
      (q * k * q⁻¹ * k⁻¹)⁻¹ := by group
  rw [e, toddA_comm D (hqK k hk) hc, mul_inv_cancel_right]

theorem image_conjClass_eq {D : ToddParabolic L} {q : G}
    (hqA : q ∈ normalizer (toddA D : Set G))
    (hqK : ∀ k ∈ toddK D, q * k * q⁻¹ * k⁻¹ ∈ toddA D) {x : G} (hx : x ∈ toddA D) :
    (fun y => q * y * q⁻¹) '' conjClass (toddK D) x = conjClass (toddK D) (q * x * q⁻¹) := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, conj_conj_eq_of_commutator_mem hqA hqK hk hx⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * x * k⁻¹, ⟨k, hk, rfl⟩, conj_conj_eq_of_commutator_mem hqA hqK hk hx⟩

theorem ncard_conjClass_conj {D : ToddParabolic L} {q : G}
    (hqA : q ∈ normalizer (toddA D : Set G))
    (hqK : ∀ k ∈ toddK D, q * k * q⁻¹ * k⁻¹ ∈ toddA D) {x : G} (hx : x ∈ toddA D) :
    (conjClass (toddK D) (q * x * q⁻¹)).ncard = (conjClass (toddK D) x).ncard := by
  rw [← image_conjClass_eq hqA hqK hx,
    Set.ncard_image_of_injective _ (fun y z hyz => by simpa using hyz)]

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem two_trans_toddK (h : Setting G L D t) {x y z w : G}
    (hx : x ∈ conjClass (toddK D) (D.a₁ : G)) (hy : y ∈ conjClass (toddK D) (D.a₁ : G))
    (hz : z ∈ conjClass (toddK D) (D.a₁ : G)) (hw : w ∈ conjClass (toddK D) (D.a₁ : G))
    (hxy : x ≠ y) (hzw : z ≠ w) : ∃ k ∈ toddK D, k * x * k⁻¹ = z ∧ k * y * k⁻¹ = w := by
  rw [conjClass_toddK] at hx hy hz hw
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', rfl⟩ := hz
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨k, hk, e1, e2⟩ := h.facts.two_trans x' hx' y' hy' z' hz' w' hw'
    (fun e => hxy (congrArg L.subtype e)) (fun e => hzw (congrArg L.subtype e))
  refine ⟨k, ⟨k, hk, rfl⟩, ?_, ?_⟩
  · rw [← e1]
    simp
  · rw [← e2]
    simp

theorem mem_toddE_of_commutator_mem (h : Setting G L D t) {q : G}
    (hqH : q ∈ centralizer ({t} : Set G)) (hqA : q ∈ normalizer (toddA D : Set G))
    (hqK : ∀ k ∈ toddK D, q * k * q⁻¹ * k⁻¹ ∈ toddA D) : q ∈ toddE D t := by
  obtain ⟨n₁, n₂, n₃⟩ := ncard_delta D (G := G)
  obtain ⟨o₁, -, -⟩ := a_ne_one D (G := G)
  have hΔA : conjClass (toddK D) (D.a₁ : G) ⊆ toddA D := conjClass_toddK_subset D D.a_mem.1
  have hperm : ∀ δ ∈ conjClass (toddK D) (D.a₁ : G),
      q * δ * q⁻¹ ∈ conjClass (toddK D) (D.a₁ : G) := by
    intro δ hδ
    have hδA := hΔA hδ
    have hqδ : q * δ * q⁻¹ ∈ toddA D := (mem_normalizer_iff.1 hqA δ).1 hδA
    have hδ1 : q * δ * q⁻¹ ≠ 1 := by
      intro h1
      have hδ1' : δ = 1 := by
        calc δ = q⁻¹ * (q * δ * q⁻¹) * q := by group
          _ = 1 := by rw [h1]; group
      obtain ⟨c, -, hc⟩ := hδ
      apply o₁
      calc (D.a₁ : G) = c⁻¹ * (c * D.a₁ * c⁻¹) * c := by group
        _ = 1 := by rw [← hc, hδ1']; group
    have hcard : (conjClass (toddK D) (q * δ * q⁻¹)).ncard = 21 := by
      rw [ncard_conjClass_conj hqA hqK hδA, conjClass_eq_of_mem hδ, n₁]
    rcases mem_delta_of_mem D hqδ hδ1 with h1 | h1 | h1
    · exact h1
    · rw [conjClass_eq_of_mem h1, n₂] at hcard
      exact absurd hcard (by norm_num)
    · rw [conjClass_eq_of_mem h1, n₃] at hcard
      exact absurd hcard (by norm_num)
  have hfix : ∀ δ ∈ conjClass (toddK D) (D.a₁ : G), q * δ * q⁻¹ = δ := by
    intro δ hδ
    by_contra hne
    have hlt : ({δ, q * δ * q⁻¹} : Set G).ncard < (conjClass (toddK D) (D.a₁ : G)).ncard := by
      rw [n₁]
      exact (Set.ncard_insert_le _ _).trans_lt (by rw [Set.ncard_singleton]; norm_num)
    obtain ⟨δ', hδ', hδ'n⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδ'n
    obtain ⟨k, hk, e1, e2⟩ :=
      h.two_trans_toddK hδ (hperm δ hδ) hδ hδ' (Ne.symm hne) (Ne.symm hδ'n.1)
    apply hδ'n.2
    rw [← e2, ← conj_conj_eq_of_commutator_mem hqA hqK hk (hΔA hδ), e1]
  have hBK : ∀ k ∈ toddK D, ∀ b ∈ toddA D ⊓ centralizer ({q} : Set G),
      k * b * k⁻¹ ∈ toddA D ⊓ centralizer ({q} : Set G) := by
    intro k hk b hb
    refine mem_inf.2 ⟨conj_mem_toddA D hk hb.1, mem_centralizer_singleton_iff.2 ?_⟩
    have hqb : q * b * q⁻¹ = b := by
      rw [← mem_centralizer_singleton_iff.1 hb.2, mul_inv_cancel_right]
    have e := conj_conj_eq_of_commutator_mem hqA hqK hk hb.1
    rw [hqb] at e
    calc k * b * k⁻¹ * q = q * (k * b * k⁻¹) * q⁻¹ * q := by rw [e]
      _ = q * (k * b * k⁻¹) := by group
  have hB1 : toddA D ⊓ centralizer ({q} : Set G) ≠ ⊥ := by
    intro hB0
    have hf := hfix _ (self_mem_conjClass _ _)
    have hmem : (D.a₁ : G) ∈ toddA D ⊓ centralizer ({q} : Set G) := by
      refine mem_inf.2 ⟨⟨_, D.a_mem.1, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
      calc (D.a₁ : G) * q = q * D.a₁ * q⁻¹ * q := by rw [hf]
        _ = q * D.a₁ := by group
    rw [hB0, mem_bot] at hmem
    exact o₁ hmem
  have hBA := h.eq_toddA_of_invariant inf_le_left hBK hB1
  refine h.mem_toddE_of_comm (fun a ha => ?_) ?_
  · have hab : a ∈ toddA D ⊓ centralizer ({q} : Set G) := by rw [hBA]; exact ha
    rw [← mem_centralizer_singleton_iff.1 hab.2, mul_inv_cancel_right]
  · rw [mem_centralizer_singleton_iff.1 hqH, mul_inv_cancel_right]

theorem le_toddE_of_isPGroup (h : Setting G L D t) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G)) (hQ2 : IsPGroup 2 Q)
    (hQK : ∀ k ∈ toddK D, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) : Q ≤ toddE D t := by
  have hR : Q ⊓ L ≤ toddA D := le_toddA_of_isPGroup D inf_le_right (hQ2.to_le inf_le_left)
    (inf_le_left.trans (hQ.trans inf_le_left))
    (fun k hk r hr => mem_inf.2 ⟨hQK k hk r hr.1, mul_mem (mul_mem (toddK_le D hk) hr.2)
      (inv_mem (toddK_le D hk))⟩)
  intro q hq
  have hqH := (hQ hq).2
  refine h.mem_toddE_of_commutator_mem hqH (hQ hq).1 fun k hk => hR (mem_inf.2 ⟨?_, ?_⟩)
  · have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem hq (hQK k hk _ (inv_mem hq))
  · exact mul_mem ((mem_normalizer_iff.1 (h.H_le hqH) k).1 (toddK_le D hk))
      (inv_mem (toddK_le D hk))

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada

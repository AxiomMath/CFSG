module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieB
import CFSG.ClassicalInvolution.Asc77.AscE187B2a
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace ChainFrame

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem inf_eq_bot_of_isPGroup_of_odd {V N : Subgroup X} (hV : IsPGroup 2 V)
    (hN : Odd (Nat.card N)) : V ⊓ N = ⊥ := by
  have h1 : IsPGroup 2 ↥(V ⊓ N) := hV.to_le inf_le_left
  obtain ⟨k, hk⟩ := h1.exists_card_eq
  have h2 : Nat.card ↥(V ⊓ N) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  have h3 : Odd (Nat.card ↥(V ⊓ N)) := hN.of_dvd_nat h2
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr (dvd_pow_self 2 hk0))
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

theorem isSylow2In_sup_odd {B N : Subgroup X} [N.Normal] (hB : IsPGroup 2 B)
    (hN : Odd (Nat.card N)) : IsSylow2In B (B ⊔ N) := by
  have hcard : ∀ V : Subgroup X, IsPGroup 2 V → Nat.card ↥(V ⊔ N) = Nat.card N * Nat.card V := by
    intro V hV
    have h := card_sup_mul_card_inf' (A := N) (C := V) (fun v _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      exact ⟨fun hn => Subgroup.Normal.conj_mem inferInstance n hn v, fun hn => by
        have := Subgroup.Normal.conj_mem inferInstance _ hn v⁻¹
        simpa [mul_assoc] using this⟩)
    rw [inf_comm, inf_eq_bot_of_isPGroup_of_odd hV hN, Subgroup.card_bot, mul_one] at h
    exact h
  refine ⟨le_sup_left, hB, fun V' hV'M hV'2 hBV' => ?_⟩
  have hle : V' ⊔ N ≤ B ⊔ N := sup_le hV'M le_sup_right
  have h1 : Nat.card ↥(V' ⊔ N) ≤ Nat.card ↥(B ⊔ N) := Subgroup.card_le_of_le hle
  rw [hcard V' hV'2, hcard B hB] at h1
  have hpos : 0 < Nat.card N := Nat.card_pos
  have h2 : Nat.card V' ≤ Nat.card B := Nat.le_of_mul_le_mul_left h1 hpos
  exact (Subgroup.eq_of_le_of_card_ge hBV' h2).symm

theorem exists_normalizing_lift {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) (S : Set X)
    (hS2 : ∀ s ∈ S, s * s = 1) (hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {n₀ : X}
    (hPS : ∀ s ∈ S, ∃ b' ∈ Subgroup.closure S,
      QuotientGroup.mk' N (n₀ * s * n₀⁻¹) = QuotientGroup.mk' N b') :
    ∃ n : X, conjSub n (Subgroup.closure S) = Subgroup.closure S ∧
      ∀ y ∈ Subgroup.closure S,
        QuotientGroup.mk' N (n * y * n⁻¹) = QuotientGroup.mk' N (n₀ * y * n₀⁻¹) := by
  set B : Subgroup X := Subgroup.closure S with hBdef
  set φ := QuotientGroup.mk' N with hφ
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := commutes_closure hSab
  have hBsq : ∀ x ∈ B, x * x = 1 := sq_closure hS2 hSab
  have hB2 : IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by simpa [sq] using hBsq g g.2)⟩
  have hP : ∀ b ∈ B, ∃ b' ∈ B, φ (n₀ * b * n₀⁻¹) = φ b' := by
    intro b hb
    refine Subgroup.closure_induction (p := fun b _ => ∃ b' ∈ B, φ (n₀ * b * n₀⁻¹) = φ b')
      hPS ⟨1, B.one_mem, by simp⟩ ?_ ?_ hb
    · rintro x y - - ⟨x', hx', hx⟩ ⟨y', hy', hy⟩
      refine ⟨x' * y', B.mul_mem hx' hy', ?_⟩
      have e : n₀ * (x * y) * n₀⁻¹ = (n₀ * x * n₀⁻¹) * (n₀ * y * n₀⁻¹) := by group
      rw [e, map_mul φ (n₀ * x * n₀⁻¹) (n₀ * y * n₀⁻¹), hx, hy, ← map_mul]
    · rintro x - ⟨x', hx', hx⟩
      refine ⟨x'⁻¹, B.inv_mem hx', ?_⟩
      have e : n₀ * x⁻¹ * n₀⁻¹ = (n₀ * x * n₀⁻¹)⁻¹ := by group
      rw [e, map_inv, map_inv, hx]
  have hPM : conjSub n₀ B ≤ B ⊔ N := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨b', hb', hbb'⟩ := hP b hb
    have h1 : b'⁻¹ * (n₀ * b * n₀⁻¹) ∈ N := by
      rw [← QuotientGroup.eq]
      exact hbb'.symm
    have h2 : (MulAut.conj n₀).toMonoidHom b = n₀ * b * n₀⁻¹ := rfl
    rw [h2, show n₀ * b * n₀⁻¹ = b' * (b'⁻¹ * (n₀ * b * n₀⁻¹)) by group]
    exact mul_mem (Subgroup.mem_sup_left hb') (Subgroup.mem_sup_right h1)
  have hSylB : IsSylow2In B (B ⊔ N) := isSylow2In_sup_odd hB2 hN
  have hP2 : IsPGroup 2 (conjSub n₀ B) := hB2.map _
  have hcardP : Nat.card ↥(conjSub n₀ B) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj n₀).injective
  have hSylP : IsSylow2In (conjSub n₀ B) (B ⊔ N) :=
    hSylB.of_natCard_le hP2 hPM hcardP.ge
  obtain ⟨y, hy, hyle⟩ := exists_conj_of_isSylow2In hSylP hSylB.2.1 hSylB.1
  have hBy : conjSub y (conjSub n₀ B) = B := by
    have hcard' : Nat.card ↥(conjSub y (conjSub n₀ B)) = Nat.card ↥B :=
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).trans hcardP
    exact (Subgroup.eq_of_le_of_card_ge hyle hcard'.le).symm
  refine ⟨y * n₀, ?_, ?_⟩
  · rw [conjSub_mul]
    exact hBy
  · intro b hb
    have hyB : ∃ c ∈ B, φ y = φ c := by
      rw [Subgroup.sup_eq_closure] at hy
      refine Subgroup.closure_induction (p := fun x _ => ∃ c ∈ B, φ x = φ c) ?_ ?_ ?_ ?_ hy
      · rintro x (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · have h1 : φ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
          exact ⟨1, B.one_mem, h1.trans (map_one φ).symm⟩
      · exact ⟨1, B.one_mem, rfl⟩
      · rintro x x' - - ⟨c, hc, hxc⟩ ⟨c', hc', hxc'⟩
        exact ⟨c * c', B.mul_mem hc hc', by rw [map_mul, map_mul, hxc, hxc']⟩
      · rintro x - ⟨c, hc, hxc⟩
        exact ⟨c⁻¹, B.inv_mem hc, by rw [map_inv, map_inv, hxc]⟩
    obtain ⟨c, hc, hyc⟩ := hyB
    obtain ⟨b', hb', hbb'⟩ := hP b hb
    have e : (y * n₀) * b * (y * n₀)⁻¹ = y * (n₀ * b * n₀⁻¹) * y⁻¹ := by group
    rw [e, map_mul, map_mul, map_inv, hbb', hyc]
    have hcomm : φ c * φ b' = φ b' * φ c := by
      rw [← map_mul, ← map_mul, hBab c hc b' hb']
    rw [hcomm]
    group

theorem injOn_mk_of_isPGroup_of_odd {N B : Subgroup X} [N.Normal] (hB : IsPGroup 2 B)
    (hN : Odd (Nat.card N)) {a b : X} (ha : a ∈ B) (hb : b ∈ B)
    (h : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  have h1 : a⁻¹ * b ∈ N := by
    rw [← QuotientGroup.eq]
    exact h
  have h2 : a⁻¹ * b ∈ B := B.mul_mem (B.inv_mem ha) hb
  have h3 : a⁻¹ * b ∈ B ⊓ N := ⟨h2, h1⟩
  rw [inf_eq_bot_of_isPGroup_of_odd hB hN, Subgroup.mem_bot] at h3
  exact (inv_mul_eq_one.mp h3)

end Sylow

theorem mem_center_of_conj_mem {K : Type*} [Group K] {x : K} (ν : K)
    (h : ν * x * ν⁻¹ ∈ Subgroup.center K) : x ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  have h1 := h (ν * g * ν⁻¹)
  have h2 : ν * (g * x) * ν⁻¹ = ν * (x * g) * ν⁻¹ := by
    calc ν * (g * x) * ν⁻¹ = (ν * g * ν⁻¹) * (ν * x * ν⁻¹) := by group
      _ = (ν * x * ν⁻¹) * (ν * g * ν⁻¹) := h1
      _ = ν * (x * g) * ν⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem commutator_eq_one_of_comm {M : Type*} [Group M] {a b : M} (h : a * b = b * a) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [h]
  group

end ChainFrame


section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : ChainCtx p f Ω z} (L : ChainLift C)

namespace ChainLift

theorem psi_comm_ne : ∃ r ∈ L.R₂, C.psi C.i₁ (L.τ₁ * r * L.τ₁⁻¹ * r⁻¹) ≠ 1 := by
  obtain ⟨r, hr, hrc⟩ := L.hd.not_central
  exact ⟨r, hr, fun h => hrc (C.psi_ker C.i₁ (MonoidHom.mem_ker.mpr h))⟩

omit [Finite G] in
theorem hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem t_ne_z : L.t ≠ z := by
  intro h
  obtain ⟨r, hr, hrc⟩ := L.psi_comm_ne
  apply hrc
  have h1 : oddQuotMk z ⟨L.t, L.ht⟩ = oddQuotMk z ⟨z, hzC⟩ := by
    congr 1
    exact Subtype.ext h
  have hcen := oddQuotMk_central hzC (C.psi C.i₁ r)
  rw [← h1, L.htbar] at hcen
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact ChainFrame.commutator_eq_one_of_comm hcen

theorem z'_ne_z : L.z' ≠ z := by
  intro h
  obtain ⟨r, hr, hrc⟩ := L.hd.not_central
  apply hrc
  apply ChainFrame.mem_center_of_conj_mem L.ν₁
  set r' := L.ν₁ * r * L.ν₁⁻¹ with hr'
  have h1 : oddQuotMk z ⟨L.z', L.hz'⟩ = oddQuotMk z ⟨z, hzC⟩ := by
    congr 1
    exact Subtype.ext h
  have hcen := oddQuotMk_central hzC (C.psi C.i₁ r')
  rw [← h1, L.hz'bar] at hcen
  have h2 : L.τ₂ * r' * L.τ₂⁻¹ * r'⁻¹ = L.ν₁ * (L.τ₁ * r * L.τ₁⁻¹ * r⁻¹) * L.ν₁⁻¹ := by
    rw [← L.hd.swap₁, hr']
    group
  rw [← h2]
  refine C.psi_ker C.i₁ (MonoidHom.mem_ker.mpr ?_)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact ChainFrame.commutator_eq_one_of_comm hcen

theorem z'_ne_t : L.z' ≠ L.t := by
  intro h
  have h1 : oddQuotMk z ⟨L.z', L.hz'⟩ = oddQuotMk z ⟨L.t, L.ht⟩ := by
    congr 1
    exact Subtype.ext h
  rw [L.hz'bar, L.htbar] at h1
  apply L.hd.prod_not_central
  apply C.psi_ker C.i₁
  rw [MonoidHom.mem_ker, map_mul, ← h1, ← map_mul, L.hd.sq₂, map_one]

theorem J_ne_K : L.J ≠ C.K := by
  intro h
  have ht : IsUniqueInvolution C.K L.t :=
    h ▸ ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt
  exact L.t_ne_z (ht.eq C.hKz)

theorem K'_ne_K : L.K' ≠ C.K := by
  intro h
  have ht : IsUniqueInvolution C.K L.z' :=
    h ▸ ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hK'z'
  exact L.z'_ne_z (ht.eq C.hKz)

theorem hperp : L.K' ∉ KPerp Ω L.J := by
  intro hmem
  rcases hmem with h | h
  · have ht : IsUniqueInvolution L.J L.z' :=
      h ▸ ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hK'z'
    exact L.z'_ne_t
      (ht.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt))
  · obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr C.hp C.hq C.hΩ.classical L.hJ.1 h
    have hat : a = L.t :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq ha).eq
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)
    have htq : L.t ∈ trivialOnQuot L.K' :=
      (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L.K')).mpr (hat ▸ hKa)
    have hq : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z L.K')) := by
      rw [L.hK'img]
      exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₁)
        (fundQuasisimple_core C.hp (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
          (C.four_le C.i₁ C.tag₁) L.R₂ L.hR₂)
    have hcen := oddQuotMk_centralizes_modOdd_exactCore L.hK'z' C.hc2 L.hK'.2 htq L.ht hq
    obtain ⟨r, hr, hrc⟩ := L.hd.not_central
    have hrm : C.psi C.i₁ r ∈ modOdd z (exactCore z L.K') := by
      rw [L.hK'img]
      exact ⟨r, hr, rfl⟩
    have h2 := hcen _ hrm
    rw [L.htbar] at h2
    apply hrc
    refine C.psi_ker C.i₁ (MonoidHom.mem_ker.mpr ?_)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact ChainFrame.commutator_eq_one_of_comm h2

theorem frameData : ChainFrameData Ω C.K L.J L.K' z L.t L.z' where
  mem := C.hK
  hz := C.hKz
  hJ := mem_omegaNbr_of_trivialOnQuot C.hp C.hq C.hΩ C.hK C.hKz L.hJ.1 L.J_ne_K L.hJ.2
  ht := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt
  hK' := mem_omegaNbr_of_trivialOnQuot C.hp C.hq C.hΩ C.hK C.hKz L.hK'.1 L.K'_ne_K L.hK'.2
  hz' := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hK'z'
  htz' := L.htz'
  hperp := L.hperp

theorem B_le_centralizer :
    Subgroup.closure ({z, L.t, L.z'} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  exacts [hzC, L.ht, L.hz']

theorem exists_swap (ν : (compModel C.D C.i₁).K) (e₁ e₂ : G)
    (he₁ : e₁ ∈ Subgroup.closure ({z, L.t, L.z'} : Set G))
    (he₂ : e₂ ∈ Subgroup.closure ({z, L.t, L.z'} : Set G))
    (h₁ : oddQuotMk z ⟨e₁, L.B_le_centralizer he₁⟩ = C.psi C.i₁ (ν * L.τ₁ * ν⁻¹))
    (h₂ : oddQuotMk z ⟨e₂, L.B_le_centralizer he₂⟩ = C.psi C.i₁ (ν * L.τ₂ * ν⁻¹)) :
    ∃ n ∈ Subgroup.normalizer ((Subgroup.closure ({z, L.t, L.z'} : Set G) : Subgroup G) : Set G),
      n * z * n⁻¹ = z ∧ n * L.t * n⁻¹ = e₁ := by
  classical
  obtain ⟨Cz, hCz⟩ : ∃ Cz : Subgroup G, Cz = Subgroup.centralizer ({z} : Set G) := ⟨_, rfl⟩
  have hzCz : z ∈ Cz := hCz ▸ hzC
  have htCz : L.t ∈ Cz := hCz ▸ L.ht
  have hz'Cz : L.z' ∈ Cz := hCz ▸ L.hz'
  subst hCz
  obtain ⟨gz, hgz, -⟩ : ∃ g : ↥(Subgroup.centralizer ({z} : Set G)), (g : G) = z ∧ True :=
    ⟨⟨z, hzC⟩, rfl, trivial⟩
  obtain ⟨gt, hgt, hφt⟩ : ∃ g : ↥(Subgroup.centralizer ({z} : Set G)), (g : G) = L.t ∧
      oddQuotMk z g = C.psi C.i₁ L.τ₁ := ⟨⟨L.t, L.ht⟩, rfl, L.htbar⟩
  obtain ⟨gz', hgz', hφz'⟩ : ∃ g : ↥(Subgroup.centralizer ({z} : Set G)), (g : G) = L.z' ∧
      oddQuotMk z g = C.psi C.i₁ L.τ₂ := ⟨⟨L.z', L.hz'⟩, rfl, L.hz'bar⟩
  set N := componentClassificationOddCore ↥(Subgroup.centralizer ({z} : Set G)) with hN
  have hodd : Odd (Nat.card N) := OddCore.odd_card _
  set S : Set ↥(Subgroup.centralizer ({z} : Set G)) := {gz, gt, gz'} with hS
  have hfd := L.frameData
  have hcg := hfd.comm_gen C.hp C.hΩ
  have hsq := hfd.sq_gen
  have hS2 : ∀ s ∈ S, s * s = 1 := by
    rintro s (rfl | rfl | rfl)
    · exact Subtype.ext (by rw [Subgroup.coe_mul, hgz]; exact hsq z (by simp))
    · exact Subtype.ext (by rw [Subgroup.coe_mul, hgt]; exact hsq L.t (by simp))
    · exact Subtype.ext (by rw [Subgroup.coe_mul, hgz']; exact hsq L.z' (by simp))
  have hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    have key : ∀ a ∈ S, (a : G) ∈ ({z, L.t, L.z'} : Set G) := by
      rintro a (rfl | rfl | rfl)
      · rw [hgz]; simp
      · rw [hgt]; simp
      · rw [hgz']; simp
    intro a ha b hb
    exact Subtype.ext (hcg _ (key a ha) _ (key b hb))
  have hmap : (Subgroup.closure S).map (Subgroup.centralizer ({z} : Set G)).subtype =
      Subgroup.closure ({z, L.t, L.z'} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [hS, Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype, hgz, hgt, hgz']
  have hBiff : ∀ x : ↥(Subgroup.centralizer ({z} : Set G)), x ∈ Subgroup.closure S ↔
      (x : G) ∈ Subgroup.closure ({z, L.t, L.z'} : Set G) := by
    intro x
    rw [← hmap]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hB2 : IsPGroup 2 (Subgroup.closure S) := by
    have hsq' := ChainFrame.sq_closure hS2 hSab
    exact fun g => ⟨1, Subtype.ext (by simpa [sq] using hsq' g g.2)⟩
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk'_surjective N (C.psi C.i₁ ν)
  have hn₀φ : oddQuotMk z n₀ = C.psi C.i₁ ν := hn₀
  have hφ₁ : QuotientGroup.mk' N (n₀ * gt * n₀⁻¹) =
      QuotientGroup.mk' N ⟨e₁, L.B_le_centralizer he₁⟩ := by
    show oddQuotMk z (n₀ * gt * n₀⁻¹) = oddQuotMk z ⟨e₁, L.B_le_centralizer he₁⟩
    rw [h₁]
    simp only [map_mul, map_inv, hn₀φ, hφt]
  have hPS : ∀ s ∈ S, ∃ b' ∈ Subgroup.closure S,
      QuotientGroup.mk' N (n₀ * s * n₀⁻¹) = QuotientGroup.mk' N b' := by
    rintro s (rfl | rfl | rfl)
    · refine ⟨s, Subgroup.subset_closure (by simp [hS]), ?_⟩
      have hc : n₀ * s = s * n₀ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hgz]
        exact Subgroup.mem_centralizer_singleton_iff.mp n₀.2
      rw [hc]
      group
    · exact ⟨⟨e₁, L.B_le_centralizer he₁⟩, (hBiff _).mpr he₁, hφ₁⟩
    · refine ⟨⟨e₂, L.B_le_centralizer he₂⟩, (hBiff _).mpr he₂, ?_⟩
      show oddQuotMk z (n₀ * s * n₀⁻¹) = oddQuotMk z ⟨e₂, L.B_le_centralizer he₂⟩
      rw [h₂]
      simp only [map_mul, map_inv, hn₀φ, hφz']
  obtain ⟨n, hn, hnφ⟩ := ChainFrame.exists_normalizing_lift hodd S hS2 hSab hPS
  refine ⟨(n : G), ?_, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hmem : ∀ y : ↥(Subgroup.centralizer ({z} : Set G)), y ∈ Subgroup.closure S ↔
        n⁻¹ * y * n ∈ Subgroup.closure S := by
      intro y
      have := mem_conjSub_iff (n := n) (K := Subgroup.closure S) (x := y)
      rw [hn] at this
      exact this
    constructor
    · intro hx
      have hxC := L.B_le_centralizer hx
      have hx' : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) ∈ Subgroup.closure S :=
        (hBiff _).mpr hx
      have h1 : n * ⟨x, hxC⟩ * n⁻¹ ∈ Subgroup.closure S := by
        rw [hmem]
        simpa [mul_assoc] using hx'
      exact (hBiff _).mp h1
    · intro hx
      have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
        have h1 := L.B_le_centralizer hx
        have h2 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈
            Subgroup.centralizer ({z} : Set G) :=
          mul_mem (mul_mem (inv_mem n.2) h1) n.2
        simpa [mul_assoc] using h2
      have hx' : n * ⟨x, hxC⟩ * n⁻¹ ∈ Subgroup.closure S := (hBiff _).mpr hx
      have h1 : ⟨x, hxC⟩ ∈ Subgroup.closure S := by
        rw [hmem] at hx'
        simpa [mul_assoc] using hx'
      exact (hBiff _).mp h1
  · have hc := Subgroup.mem_centralizer_singleton_iff.mp n.2
    rw [hc]
    group
  · have hgtS : gt ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
    have h1 : n * gt * n⁻¹ ∈ Subgroup.closure S := by
      have : n * gt * n⁻¹ ∈ conjSub n (Subgroup.closure S) := ⟨gt, hgtS, rfl⟩
      rwa [hn] at this
    have h2 := hnφ gt hgtS
    rw [hφ₁] at h2
    have h3 := ChainFrame.injOn_mk_of_isPGroup_of_odd hB2 hodd h1
      ((hBiff _).mpr he₁) h2
    have h4 := congrArg Subtype.val h3
    simpa [hgt] using h4

theorem t_mem_B : L.t ∈ Subgroup.closure ({z, L.t, L.z'} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem z'_mem_B : L.z' ∈ Subgroup.closure ({z, L.t, L.z'} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem z_mem_B : z ∈ Subgroup.closure ({z, L.t, L.z'} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem symm : ChainFrameSymm z L.t L.z' := by
  refine ⟨fun e he => ?_⟩
  rcases he with rfl | rfl
  · exact L.exists_swap L.ν₁ L.z' L.t L.z'_mem_B L.t_mem_B
      (by rw [L.hz'bar, L.hd.swap₁]) (by rw [L.htbar, L.hd.swap₁'])
  · refine L.exists_swap L.ν₂ (L.t * L.z') L.z' (Subgroup.mul_mem _ L.t_mem_B L.z'_mem_B)
      L.z'_mem_B ?_ (by rw [L.hz'bar, L.hd.swap₂'])
    have : (⟨L.t * L.z', L.B_le_centralizer (Subgroup.mul_mem _ L.t_mem_B L.z'_mem_B)⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) = ⟨L.t, L.ht⟩ * ⟨L.z', L.hz'⟩ := rfl
    rw [this, map_mul, L.htbar, L.hz'bar, L.hd.swap₂, map_mul]

theorem toralOnComponent :
    FrameVertex.ToralOnComponent z (Subgroup.closure ({z, L.t, L.z'} : Set G))
      (C.psi C.i₁) := by
  have hpair : ∀ a ∈ ({L.τ₁, L.τ₂} : Set (compModel C.D C.i₁).K),
      ∀ b ∈ ({L.τ₁, L.τ₂} : Set (compModel C.D C.i₁).K), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact L.hd.comm
    · exact L.hd.comm.symm
    · rfl
  have hcm := ChainFrame.commutes_closure hpair
  refine ⟨Subgroup.closure ({L.τ₁, L.τ₂} : Set (compModel C.D C.i₁).K), hcm, ?_⟩
  intro b hb hbC
  have key : ∀ (b : G) (hb : b ∈ Subgroup.closure ({z, L.t, L.z'} : Set G)),
      ∃ x ∈ Subgroup.closure ({L.τ₁, L.τ₂} : Set (compModel C.D C.i₁).K), x * x = 1 ∧
        ∀ y ∈ (C.psi C.i₁).range,
          oddQuotMk z ⟨b, L.B_le_centralizer hb⟩ * y *
              (oddQuotMk z ⟨b, L.B_le_centralizer hb⟩)⁻¹ =
            C.psi C.i₁ x * y * (C.psi C.i₁ x)⁻¹ := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · refine ⟨1, Subgroup.one_mem _, by simp, fun y _ => ?_⟩
        have := oddQuotMk_central hzC y
        rw [this, mul_inv_cancel_right]
        simp
      · exact ⟨L.τ₁, Subgroup.subset_closure (by simp), L.hd.sq₁, fun y _ => by rw [L.htbar]⟩
      · exact ⟨L.τ₂, Subgroup.subset_closure (by simp), L.hd.sq₂, fun y _ => by rw [L.hz'bar]⟩
    | one =>
      refine ⟨1, Subgroup.one_mem _, by simp, fun y _ => ?_⟩
      have : (⟨1, L.B_le_centralizer (Subgroup.one_mem _)⟩ :
          ↥(Subgroup.centralizer ({z} : Set G))) = 1 := rfl
      rw [this]
      simp
    | mul x y hx hy ihx ihy =>
      obtain ⟨xa, hxa, hxa2, hact⟩ := ihx
      obtain ⟨xb, hxb, hxb2, hbct⟩ := ihy
      have hxC := L.B_le_centralizer hx
      have hyC := L.B_le_centralizer hy
      refine ⟨xa * xb, Subgroup.mul_mem _ hxa hxb, ?_, fun w hw => ?_⟩
      · calc xa * xb * (xa * xb) = xa * (xb * xa) * xb := by group
          _ = xa * (xa * xb) * xb := by rw [hcm xb hxb xa hxa]
          _ = (xa * xa) * (xb * xb) := by group
          _ = 1 := by rw [hxa2, hxb2]; simp
      · have hmul : (⟨x * y, L.B_le_centralizer (Subgroup.mul_mem _ hx hy)⟩ :
            ↥(Subgroup.centralizer ({z} : Set G))) = ⟨x, hxC⟩ * ⟨y, hyC⟩ := rfl
        rw [hmul, map_mul]
        obtain ⟨k, rfl⟩ := hw
        have hw' : C.psi C.i₁ xb * C.psi C.i₁ k * (C.psi C.i₁ xb)⁻¹ ∈ (C.psi C.i₁).range :=
          ⟨xb * k * xb⁻¹, by simp⟩
        have h1 := hbct (C.psi C.i₁ k) ⟨k, rfl⟩
        have h2 := hact _ hw'
        calc oddQuotMk z ⟨x, hxC⟩ * oddQuotMk z ⟨y, hyC⟩ * C.psi C.i₁ k *
              (oddQuotMk z ⟨x, hxC⟩ * oddQuotMk z ⟨y, hyC⟩)⁻¹
            = oddQuotMk z ⟨x, hxC⟩ * (oddQuotMk z ⟨y, hyC⟩ * C.psi C.i₁ k *
                (oddQuotMk z ⟨y, hyC⟩)⁻¹) * (oddQuotMk z ⟨x, hxC⟩)⁻¹ := by group
          _ = C.psi C.i₁ (xa * xb) * C.psi C.i₁ k * (C.psi C.i₁ (xa * xb))⁻¹ := by
            rw [h1, h2]
            simp only [map_mul]
            group
    | inv x hx ihx =>
      obtain ⟨xa, hxa, hxa2, hact⟩ := ihx
      refine ⟨xa, hxa, hxa2, fun w hw => ?_⟩
      have hxC := L.B_le_centralizer hx
      have hinv : (⟨x⁻¹, L.B_le_centralizer (Subgroup.inv_mem _ hx)⟩ :
          ↥(Subgroup.centralizer ({z} : Set G))) = ⟨x, hxC⟩⁻¹ := rfl
      rw [hinv, map_inv, inv_inv]
      have hψ : C.psi C.i₁ xa * C.psi C.i₁ xa = 1 := by rw [← map_mul, hxa2, map_one]
      have hψinv : (C.psi C.i₁ xa)⁻¹ = C.psi C.i₁ xa := inv_eq_of_mul_eq_one_right hψ
      obtain ⟨k, rfl⟩ := hw
      have hw' : C.psi C.i₁ xa * C.psi C.i₁ k * C.psi C.i₁ xa ∈ (C.psi C.i₁).range :=
        ⟨xa * k * xa, by simp⟩
      have h2 := hact _ hw'
      rw [hψinv] at h2
      have e1 : oddQuotMk z ⟨x, hxC⟩ * (C.psi C.i₁ xa * C.psi C.i₁ k * C.psi C.i₁ xa) *
          (oddQuotMk z ⟨x, hxC⟩)⁻¹ = C.psi C.i₁ k := by
        rw [h2]
        calc C.psi C.i₁ xa * (C.psi C.i₁ xa * C.psi C.i₁ k * C.psi C.i₁ xa) * C.psi C.i₁ xa
            = (C.psi C.i₁ xa * C.psi C.i₁ xa) * C.psi C.i₁ k *
                (C.psi C.i₁ xa * C.psi C.i₁ xa) := by group
          _ = C.psi C.i₁ k := by rw [hψ]; simp
      rw [hψinv]
      calc (oddQuotMk z ⟨x, hxC⟩)⁻¹ * C.psi C.i₁ k * oddQuotMk z ⟨x, hxC⟩
          = (oddQuotMk z ⟨x, hxC⟩)⁻¹ * (oddQuotMk z ⟨x, hxC⟩ *
              (C.psi C.i₁ xa * C.psi C.i₁ k * C.psi C.i₁ xa) * (oddQuotMk z ⟨x, hxC⟩)⁻¹) *
              oddQuotMk z ⟨x, hxC⟩ := by rw [e1]
        _ = C.psi C.i₁ xa * C.psi C.i₁ k * C.psi C.i₁ xa := by group
  exact key b hb

theorem not_movedByAll_of_ne {j : Fin C.D.card} (hj : j ≠ C.i₁) :
    ¬ MovedByAll (Subgroup.closure ({z, L.t, L.z'} : Set G)) z (C.psi j).range := by
  intro hmov
  have hfd := L.frameData
  have hB := hfd.isElemAbelian C.hp C.hΩ
  have hzB : z ∈ Subgroup.closure ({z, L.t, L.z'} : Set G) := L.z_mem_B
  have htB : L.t ∈ Subgroup.closure ({z, L.t, L.z'} : Set G) := L.t_mem_B
  have hnot : oddQuotMk z ⟨L.t, L.ht⟩ ∉ modOdd z (Subgroup.zpowers z) :=
    Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hfd.hz.ne_one htB hfd.ht.ne_one
      (hfd.t_ne_z C.hp C.hq C.hΩ) L.ht
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ := hmov _ (oddQuotMk_mem_modOdd htB L.ht) hnot
  apply hy
  rw [L.htbar]
  have := C.D.commute C.i₁ j hj.symm L.τ₁ k
  exact (map_mul (sectionQuotientHom C.hs.normalizes) _ _).symm.trans
    ((congrArg (sectionQuotientHom C.hs.normalizes) this).trans
      (map_mul (sectionQuotientHom C.hs.normalizes) _ _))

theorem toral : ChainToral p f C.hΩ.conjInvariant z L.t L.z' := by
  refine ⟨C.D, fun j hmov => ?_⟩
  by_cases hj : j = C.i₁
  · subst hj
    exact ⟨C.tag₁, L.toralOnComponent⟩
  · exact absurd hmov (L.not_movedByAll_of_ne hj)

end ChainLift

end Lift

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79s

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma conjSub_inv_conjSub (x : G) (A : Subgroup G) :
    conjSub x⁻¹ (conjSub x A) = A := by
  unfold conjSub
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id G := by
    ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

private lemma conjSub_self_conjSub_of_sq_one {t : G} (ht : t ^ 2 = 1) (A : Subgroup G) :
    conjSub t (conjSub t A) = A := by
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht'
  simpa only [htinv] using conjSub_inv_conjSub t A

private lemma conj_self_apply_of_sq_one {t : G} (ht : t ^ 2 = 1) (x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = (t * t) * x * (t * t)⁻¹ := by rw [mul_inv_rev]
    _ = x := by rw [ht', inv_one, one_mul, mul_one]

private lemma mem_conjSub_of_mem {c : G} {Y : Subgroup G} {x : G} (hx : x ∈ Y) :
    c * x * c⁻¹ ∈ conjSub c Y := by
  unfold conjSub
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

private lemma mem_sup_iff_exists_mul_of_commute {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  refine ⟨fun hx ↦ ?_, fun ⟨a, ha, b, hb, h⟩ ↦ h ▸ mul_mem_sup ha hb⟩
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        exact ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, by
          calc (a1 * a2) * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
            _ = a1 * (b1 * a2) * b2 := by rw [hc a2 ha2 b1 hb1]
            _ = (a1 * b1) * (a2 * b2) := by group⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by
          rw [mul_inv_rev, ← hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]⟩ }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha ↦ ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb ↦ ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

private lemma eq_of_mul_eq_mul_of_inf_bot {A B : Subgroup G} (hinf : A ⊓ B = ⊥)
    {a1 a2 b1 b2 : G} (ha1 : a1 ∈ A) (hb1 : b1 ∈ B) (ha2 : a2 ∈ A) (hb2 : b2 ∈ B)
    (h : a1 * b1 = a2 * b2) : a1 = a2 ∧ b1 = b2 := by
  have h' : a2⁻¹ * a1 = b2 * b1⁻¹ := by
    calc a2⁻¹ * a1 = a2⁻¹ * (a1 * b1) * b1⁻¹ := by group
      _ = a2⁻¹ * (a2 * b2) * b1⁻¹ := by rw [h]
      _ = b2 * b1⁻¹ := by group
  have hmem : a2⁻¹ * a1 ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha2) ha1, h'.symm ▸ B.mul_mem hb2 (B.inv_mem hb1)⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  have ha : a1 = a2 := by
    calc a1 = a2 * (a2⁻¹ * a1) := by group
      _ = a2 := by rw [hmem, mul_one]
  have hb : b1 = b2 := by
    rw [ha] at h
    exact mul_left_cancel h
  exact ⟨ha, hb⟩

theorem y7c_comm_conjSub (x : G) (A : Subgroup G) :
    conjSub x ⁅A, A⁆ = ⁅conjSub x A, conjSub x A⁆ := by
  simp only [conjSub, Subgroup.map_commutator]

theorem y7c_normalizer_comm {A : Subgroup G} {x : G} (hx : x ∈ normalizer (A : Set G)) :
    x ∈ normalizer ((⁅A, A⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  rw [Subgroup.map_commutator, hx]

theorem y7c_direct {M L1 L2 : Subgroup G} (h : Gl3Pair M L1 L2)
    (h1 : ⁅L1, L1⁆ ⊓ M = centIn M L2) (h2 : ⁅L2, L2⁆ ⊓ M = centIn M L1)
    (hinf : centIn M L1 ⊓ centIn M L2 = ⊥) (hsup : centIn M L1 ⊔ centIn M L2 = M) :
    IsInternalDirect (L1 ⊔ L2) ⁅L1, L1⁆ ⁅L2, L2⁆ := by
  have hM : M ≤ ⁅L1, L1⁆ ⊔ ⁅L2, L2⁆ := by
    rw [← hsup]
    exact sup_le ((h2 ▸ inf_le_left).trans le_sup_right)
      ((h1 ▸ inf_le_left).trans le_sup_left)
  have hL1 : L1 ≤ ⁅L1, L1⁆ ⊔ ⁅L2, L2⁆ := by
    calc L1 = ⁅L1, L1⁆ ⊔ M := (IsGL3Ext.comm_sup_eq h.ext1).symm
      _ ≤ ⁅L1, L1⁆ ⊔ ⁅L2, L2⁆ := sup_le le_sup_left hM
  have hL2 : L2 ≤ ⁅L1, L1⁆ ⊔ ⁅L2, L2⁆ := by
    calc L2 = ⁅L2, L2⁆ ⊔ M := (IsGL3Ext.comm_sup_eq h.ext2).symm
      _ ≤ ⁅L1, L1⁆ ⊔ ⁅L2, L2⁆ := sup_le le_sup_right hM
  have hbot : ⁅L1, L1⁆ ⊓ ⁅L2, L2⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hXM : ⁅L1, L1⁆ ⊓ ⁅L2, L2⁆ ≤ M := by
      rw [← h.inf]
      exact le_inf (inf_le_left.trans (commutator_le_of_le (le_refl L1) (le_refl L1)))
        (inf_le_right.trans (commutator_le_of_le (le_refl L2) (le_refl L2)))
    have hsub : ⁅L1, L1⁆ ⊓ ⁅L2, L2⁆ ≤ (⁅L1, L1⁆ ⊓ M) ⊓ (⁅L2, L2⁆ ⊓ M) :=
      le_inf (le_inf inf_le_left hXM) (le_inf inf_le_right hXM)
    have hinf' : centIn M L2 ⊓ centIn M L1 = ⊥ := by rw [inf_comm]; exact hinf
    rw [h1, h2, hinf'] at hsub
    exact hsub
  refine ⟨le_antisymm (sup_le ?_ ?_) (sup_le hL1 hL2), hbot, ?_⟩
  · exact (commutator_le_of_le (le_refl L1) (le_refl L1)).trans le_sup_left
  · exact (commutator_le_of_le (le_refl L2) (le_refl L2)).trans le_sup_right
  · intro u hu v hv
    have hcomm1 : ⁅L1, L1⁆ ≤ L1 := commutator_le_of_le (le_refl L1) (le_refl L1)
    have hcomm2 : ⁅L2, L2⁆ ≤ L2 := commutator_le_of_le (le_refl L2) (le_refl L2)
    have hnormu : u ∈ normalizer ((⁅L2, L2⁆ : Subgroup G) : Set G) :=
      y7c_normalizer_comm (h.L1_le_normalizer_L2 (hcomm1 hu))
    have hmem2 : u * v * u⁻¹ * v⁻¹ ∈ ⁅L2, L2⁆ :=
      (⁅L2, L2⁆).mul_mem ((Subgroup.mem_normalizer_iff.mp hnormu v).mp hv)
        ((⁅L2, L2⁆).inv_mem hv)
    have hnormv : v ∈ normalizer ((⁅L1, L1⁆ : Subgroup G) : Set G) :=
      y7c_normalizer_comm (h.symm.L1_le_normalizer_L2 (hcomm2 hv))
    have hmem1 : u * v * u⁻¹ * v⁻¹ ∈ ⁅L1, L1⁆ := by
      have := (⁅L1, L1⁆).mul_mem hu
        ((Subgroup.mem_normalizer_iff.mp hnormv u⁻¹).mp ((⁅L1, L1⁆).inv_mem hu))
      simpa only [mul_assoc] using this
    have hone : u * v * u⁻¹ * v⁻¹ = 1 := by
      have hmem : u * v * u⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hmem1, hmem2⟩
      simpa using hmem
    calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
      _ = v * u := by rw [hone, one_mul]

theorem y7c_centEl_equiv {K A B : Subgroup G} {t : G} (hd : IsInternalDirect K A B)
    (hAB : conjSub t A = B) (ht : t ^ 2 = 1) : Nonempty (↥A ≃* ↥(centEl K t)) := by
  obtain ⟨hsup, hinf, hc⟩ := hd
  have hAK : A ≤ K := hsup ▸ le_sup_left
  have hBK : B ≤ K := hsup ▸ le_sup_right
  have hb_mem : ∀ a : ↥A, t * (a : G) * t⁻¹ ∈ B := by
    intro a
    have := mem_conjSub_of_mem (c := t) a.2
    rwa [hAB] at this
  let φ : ↥A →* ↥(centEl K t) :=
    { toFun := fun a =>
        ⟨(a : G) * (t * (a : G) * t⁻¹), by
          refine ⟨K.mul_mem (hAK a.2) (hBK (hb_mem a)), ?_⟩
          show (a : G) * (t * (a : G) * t⁻¹) ∈ centralizer ({t} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hx : t * ((a : G) * (t * (a : G) * t⁻¹)) * t⁻¹ =
              (a : G) * (t * (a : G) * t⁻¹) := by
            calc t * ((a : G) * (t * (a : G) * t⁻¹)) * t⁻¹
                = (t * (a : G) * t⁻¹) * (t * (t * (a : G) * t⁻¹) * t⁻¹) := by group
              _ = (t * (a : G) * t⁻¹) * (a : G) := by
                    rw [conj_self_apply_of_sq_one ht (a : G)]
              _ = (a : G) * (t * (a : G) * t⁻¹) :=
                    (hc (a : G) a.2 (t * (a : G) * t⁻¹) (hb_mem a)).symm
          calc ((a : G) * (t * (a : G) * t⁻¹)) * t
              = (t * ((a : G) * (t * (a : G) * t⁻¹)) * t⁻¹) * t := by rw [hx]
            _ = t * ((a : G) * (t * (a : G) * t⁻¹)) := by group⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ((a : G) * (b : G)) * (t * ((a : G) * (b : G)) * t⁻¹) =
          ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹))
        calc ((a : G) * (b : G)) * (t * ((a : G) * (b : G)) * t⁻¹)
            = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹) := by
              group
          _ = (a : G) * ((t * (a : G) * t⁻¹) * (b : G)) * (t * (b : G) * t⁻¹) := by
              rw [hc (b : G) b.2 (t * (a : G) * t⁻¹) (hb_mem a)]
          _ = ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹)) := by
              group) }
  have hinj : Function.Injective φ := by
    intro a b hab
    have hval : (a : G) * (t * (a : G) * t⁻¹) = (b : G) * (t * (b : G) * t⁻¹) :=
      congrArg Subtype.val hab
    exact Subtype.ext (eq_of_mul_eq_mul_of_inf_bot hinf a.2 (hb_mem a) b.2 (hb_mem b) hval).1
  have hsurj : Function.Surjective φ := by
    intro k
    have hkAB : (k : G) ∈ A ⊔ B := hsup.symm ▸ k.2.1
    obtain ⟨a0, ha0, b0, hb0, hk⟩ := (mem_sup_iff_exists_mul_of_commute hc).mp hkAB
    have hkt : (k : G) * t = t * (k : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp k.2.2
    have htk : t * (k : G) * t⁻¹ = (k : G) := by rw [← hkt]; group
    have hta : t * b0 * t⁻¹ ∈ A := by
      have h' : conjSub t B = A := by
        rw [← hAB, conjSub_self_conjSub_of_sq_one ht A]
      rw [← h']
      exact mem_conjSub_of_mem hb0
    have htb : t * a0 * t⁻¹ ∈ B := by
      have := mem_conjSub_of_mem (c := t) ha0
      rwa [hAB] at this
    have hprod : (t * a0 * t⁻¹) * (t * b0 * t⁻¹) = (k : G) := by
      have hconj : t * (k : G) * t⁻¹ = (t * a0 * t⁻¹) * (t * b0 * t⁻¹) := by
        rw [← hk]; group
      rw [← hconj, htk]
    have hEq : a0 * b0 = (t * b0 * t⁻¹) * (t * a0 * t⁻¹) := by
      rw [hc (t * b0 * t⁻¹) hta (t * a0 * t⁻¹) htb, hprod, hk]
    have ha0eq : a0 = t * b0 * t⁻¹ :=
      (eq_of_mul_eq_mul_of_inf_bot hinf ha0 hb0 hta htb hEq).1
    have hta0 : t * a0 * t⁻¹ = b0 := by
      rw [ha0eq, conj_self_apply_of_sq_one ht b0]
    refine ⟨⟨a0, ha0⟩, ?_⟩
    apply Subtype.ext
    change a0 * (t * a0 * t⁻¹) = (k : G)
    rw [hta0]
    exact hk
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem y7c_centEl_eq {K A B J : Subgroup G} {t : G} (hd : IsInternalDirect K A B)
    (hAB : conjSub t A = B) (ht : t ^ 2 = 1) (hJK : J ≤ K) (hJt : ∀ j ∈ J, j * t = t * j)
    (hcard : Nat.card J = Nat.card A) : centEl K t = J := by
  have hJle : J ≤ centEl K t := by
    intro j hj
    exact ⟨hJK hj, Subgroup.mem_centralizer_singleton_iff.mpr (hJt j hj)⟩
  obtain ⟨e⟩ := y7c_centEl_equiv hd hAB ht
  have hcard2 : Nat.card ↥(centEl K t) = Nat.card J :=
    (Nat.card_congr e.toEquiv).symm.trans hcard.symm
  exact (Subgroup.eq_of_le_of_card_ge hJle hcard2.le).symm

end CFSG.OddStandard.HigherRank.YamadaG23

module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GroupTheory.FixedPointQuotientCard

public section

namespace CFSG.GroupTheory

universe u

variable {G : Type*} [Group G]

theorem mem_center_of_pow_three_mem_center
    (hcube : Function.Bijective (fun g : G => g ^ 3)) {w : G}
    (hw : w ^ 3 ∈ Subgroup.center G) : w ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hw ⊢
  intro g
  have hgz : g * w ^ 3 * g⁻¹ = w ^ 3 := by
    rw [hw g, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : g * w * g⁻¹ = w := by
    apply hcube.1
    change (g * w * g⁻¹) ^ 3 = w ^ 3
    rw [conj_pow, hgz]
  calc
    g * w = (g * w * g⁻¹) * g := by group
    _ = w * g := by rw [hconj]

theorem bijective_pow_three_quotient_center
    (hcube : Function.Bijective (fun g : G => g ^ 3)) :
    Function.Bijective (fun q : G ⧸ Subgroup.center G => q ^ 3) := by
  classical
  let Z : Subgroup G := Subgroup.center G
  constructor
  · intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | H x =>
      induction q₂ using QuotientGroup.induction_on with
      | H y =>
        have hmk : ((x ^ 3 : G) : G ⧸ Z) = ((y ^ 3 : G) : G ⧸ Z) := by
          simpa [QuotientGroup.mk_pow] using h
        have hz : (x ^ 3)⁻¹ * y ^ 3 ∈ Z := (QuotientGroup.eq).mp hmk
        obtain ⟨c, hc⟩ := hcube.2 ((x ^ 3)⁻¹ * y ^ 3)
        have hc' : c ^ 3 = (x ^ 3)⁻¹ * y ^ 3 := hc
        have hcZ : c ∈ Z := mem_center_of_pow_three_mem_center hcube (by rw [hc']; exact hz)
        have hcx : c * x = y := by
          apply hcube.1
          have hc_comm_x : Commute c x := (Subgroup.mem_center_iff.mp hcZ x).symm
          calc
            (c * x) ^ 3 = c ^ 3 * x ^ 3 := Commute.mul_pow hc_comm_x 3
            _ = ((x ^ 3)⁻¹ * y ^ 3) * x ^ 3 := by rw [hc']
            _ = x ^ 3 * ((x ^ 3)⁻¹ * y ^ 3) :=
              (Subgroup.mem_center_iff.mp hz (x ^ 3)).symm
            _ = y ^ 3 := by group
        change (x : G ⧸ Z) = (y : G ⧸ Z)
        rw [← hcx]
        simp [hcZ]
  · intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨x, hx⟩ := hcube.2 y
      have hx' : x ^ 3 = y := hx
      refine ⟨(x : G ⧸ Z), ?_⟩
      change ((x : G ⧸ Z) ^ 3) = ((y : G) : G ⧸ Z)
      rw [← QuotientGroup.mk_pow, hx']

theorem exists_inv_mul_aut_of_mul_comm
    (hcomm : ∀ x y : G, x * y = y * x)
    (α : MulAut G) (hα : α ^ 3 = 1)
    (hcube : Function.Bijective (fun g : G => g ^ 3))
    {u : G} (hu : u * α u * α (α u) = 1) :
    ∃ v : G, u = v⁻¹ * α v := by
  let : CommGroup G := CommGroup.mk hcomm
  have hα3 : α (α (α u)) = u := by
    have h := congrArg (fun f : MulAut G => f u) hα
    rw [show α ^ 3 = α * α * α by rw [pow_succ, pow_succ, pow_one],
      MulAut.mul_apply, MulAut.mul_apply] at h
    simpa using h
  obtain ⟨b, hb⟩ := hcube.2 ((u ^ 2)⁻¹ * (α u)⁻¹)
  have hb' : b ^ 3 = (u ^ 2)⁻¹ * (α u)⁻¹ := hb
  refine ⟨b, ?_⟩
  have hnorm : (α u)⁻¹ * (α (α u))⁻¹ = u := by
    have h1 : α u * α (α u) = u⁻¹ := by
      have := congrArg (fun t => u⁻¹ * t) hu
      simpa [mul_assoc] using this
    have := congrArg Inv.inv h1
    simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using this
  have hmain : (b⁻¹ * α b) ^ 3 = u ^ 3 := by
    calc
      (b⁻¹ * α b) ^ 3 = (b ^ 3)⁻¹ * α (b ^ 3) := by
        rw [mul_pow, inv_pow, ← map_pow]
      _ = ((u ^ 2)⁻¹ * (α u)⁻¹)⁻¹ * α ((u ^ 2)⁻¹ * (α u)⁻¹) := by rw [hb']
      _ = u ^ 3 := by
        rw [show ((u ^ 2)⁻¹ * (α u)⁻¹)⁻¹ * α ((u ^ 2)⁻¹ * (α u)⁻¹)
              = u ^ 2 * ((α u)⁻¹ * (α (α u))⁻¹) by
              calc
                ((u ^ 2)⁻¹ * (α u)⁻¹)⁻¹ * α ((u ^ 2)⁻¹ * (α u)⁻¹)
                    = u ^ 2 * ((α u * ((α u) ^ 2)⁻¹) * (α (α u))⁻¹) := by
                      simp only [map_mul, map_inv, map_pow, mul_inv_rev, inv_inv]
                      rw [mul_comm (α u) (u ^ 2)]
                      group
                _ = u ^ 2 * ((α u)⁻¹ * (α (α u))⁻¹) := by
                      rw [show α u * ((α u) ^ 2)⁻¹ = (α u)⁻¹ by group]]
        rw [hnorm]
        group
  exact (hcube.1 hmain).symm

theorem apply_three_eq_self_of_pow_three_eq_one
    (α : MulAut G) (hα : α ^ 3 = 1) (x : G) :
    α (α (α x)) = x := by
  have h := congrArg (fun f : MulAut G => f x) hα
  rw [show α ^ 3 = α * α * α by rw [pow_succ, pow_succ, pow_one],
    MulAut.mul_apply, MulAut.mul_apply] at h
  simpa using h

theorem norm_inv_mul_aut (α : MulAut G) (hα : α ^ 3 = 1) (v : G) :
    (v⁻¹ * α v) * α (v⁻¹ * α v) * α (α (v⁻¹ * α v)) = 1 := by
  rw [map_mul, map_inv, map_mul, map_inv,
    apply_three_eq_self_of_pow_three_eq_one α hα v]
  group

theorem norm_mul_of_mem_center
    (α : MulAut G) {c : G} (hc : c ∈ Subgroup.center G) (w : G) :
    (w * c) * α (w * c) * α (α (w * c)) =
      (w * α w * α (α w)) * (c * α c * α (α c)) := by
  have hc_comm : ∀ g : G, c * g = g * c :=
    fun g => (Subgroup.mem_center_iff.mp hc g).symm
  have hαc_mem : α c ∈ Subgroup.center G := by
    rw [← Subgroup.map_center_eq α]
    exact Subgroup.mem_map_of_mem α.toMonoidHom hc
  have hαc_comm : ∀ g : G, α c * g = g * α c :=
    fun g => (Subgroup.mem_center_iff.mp hαc_mem g).symm
  rw [map_mul, map_mul]
  calc
    (w * c) * (α w * α c) * (α (α w) * α (α c))
        = w * (c * α w) * α c * α (α w) * α (α c) := by group
    _ = w * (α w * c) * α c * α (α w) * α (α c) := by rw [hc_comm (α w)]
    _ = w * α w * c * α c * α (α w) * α (α c) := by group
    _ = w * α w * c * (α c * α (α w)) * α (α c) := by group
    _ = w * α w * c * (α (α w) * α c) * α (α c) := by rw [hαc_comm (α (α w))]
    _ = w * α w * c * α (α w) * α c * α (α c) := by group
    _ = w * α w * (c * α (α w)) * α c * α (α c) := by group
    _ = w * α w * (α (α w) * c) * α c * α (α c) := by rw [hc_comm (α (α w))]
    _ = (w * α w * α (α w)) * (c * α c * α (α c)) := by group

theorem inv_mul_aut_mul_of_mem_center
    (α : MulAut G) {d : G} (hd : d ∈ Subgroup.center G) (v : G) :
    (v * d)⁻¹ * α (v * d) = (v⁻¹ * α v) * (d⁻¹ * α d) := by
  have hd_inv_mem : d⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hd
  have hd_inv_comm : ∀ g : G, d⁻¹ * g = g * d⁻¹ :=
    fun g => (Subgroup.mem_center_iff.mp hd_inv_mem g).symm
  have hαd_mem : α d ∈ Subgroup.center G := by
    rw [← Subgroup.map_center_eq α]
    exact Subgroup.mem_map_of_mem α.toMonoidHom hd
  rw [mul_inv_rev, map_mul]
  calc
    d⁻¹ * v⁻¹ * (α v * α d) = (d⁻¹ * (v⁻¹ * α v)) * α d := by group
    _ = ((v⁻¹ * α v) * d⁻¹) * α d := by rw [hd_inv_comm (v⁻¹ * α v)]
    _ = (v⁻¹ * α v) * (d⁻¹ * α d) := by group

theorem exists_inv_mul_aut_of_nilpotencyClass_le (n : ℕ) :
    ∀ (G : Type u) [Group G] [Group.IsNilpotent G],
      Group.nilpotencyClass G ≤ n →
      ∀ (α : MulAut G), α ^ 3 = 1 → Function.Bijective (fun g : G => g ^ 3) →
      ∀ u : G, u * α u * α (α u) = 1 → ∃ v : G, u = v⁻¹ * α v := by
  induction n with
  | zero =>
      intro G _ _ hclass α hα hcube u hu
      have hzero : Group.nilpotencyClass G = 0 := Nat.le_zero.mp hclass
      let : Subsingleton G := (Group.nilpotencyClass_zero_iff_subsingleton).mp hzero
      exact ⟨1, Subsingleton.elim u (1⁻¹ * α 1)⟩
  | succ n ih =>
      intro G _ _ hclass α hα hcube u hu
      let Z : Subgroup G := Subgroup.center G
      let Q := G ⧸ Z
      have : Group.IsNilpotent Q := Group.nilpotent_quotient_of_nilpotent Z
      have hclQ : Group.nilpotencyClass Q = Group.nilpotencyClass G - 1 := by
        dsimp [Q, Z]
        exact Group.nilpotencyClass_quotient_center
      have hclassQ : Group.nilpotencyClass Q ≤ n := by
        rw [hclQ]
        exact (Nat.sub_le_iff_le_add).mpr hclass
      let αQ : MulAut Q := CFSG.quotientAut α
      have hαQ : αQ ^ 3 = 1 := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H x =>
          change (αQ ^ 3) (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z x
          rw [show αQ ^ 3 = αQ * αQ * αQ by rw [pow_succ, pow_succ, pow_one]]
          rw [MulAut.mul_apply, MulAut.mul_apply]
          show (CFSG.quotientAut α) ((CFSG.quotientAut α) ((CFSG.quotientAut α)
            (QuotientGroup.mk' (Subgroup.center G) x))) =
            QuotientGroup.mk' (Subgroup.center G) x
          simp only [CFSG.quotientAut_mk]
          rw [apply_three_eq_self_of_pow_three_eq_one α hα x]
      have hcubeQ : Function.Bijective (fun q : Q => q ^ 3) := by
        dsimp [Q, Z]
        exact bijective_pow_three_quotient_center hcube
      have huQ : (QuotientGroup.mk' Z u) * αQ (QuotientGroup.mk' Z u) *
          αQ (αQ (QuotientGroup.mk' Z u)) = 1 := by
        have h1 : αQ (QuotientGroup.mk' Z u) = QuotientGroup.mk' Z (α u) := by
          change (CFSG.quotientAut α) (QuotientGroup.mk' (Subgroup.center G) u) =
            QuotientGroup.mk' (Subgroup.center G) (α u)
          rw [CFSG.quotientAut_mk]
        have h3 : αQ (QuotientGroup.mk' Z (α u)) =
            QuotientGroup.mk' Z (α (α u)) := by
          change (CFSG.quotientAut α) (QuotientGroup.mk' (Subgroup.center G) (α u)) =
            QuotientGroup.mk' (Subgroup.center G) (α (α u))
          rw [CFSG.quotientAut_mk]
        rw [h1, h3]
        change QuotientGroup.mk' Z (u * α u * α (α u)) = 1
        rw [hu, map_one]
      obtain ⟨vQ, hvQ⟩ := ih Q hclassQ αQ hαQ hcubeQ (QuotientGroup.mk' Z u) huQ
      obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective Z vQ
      rw [← hv] at hvQ
      let w : G := v⁻¹ * α v
      have hq : QuotientGroup.mk' Z u = QuotientGroup.mk' Z w := by
        calc
          QuotientGroup.mk' Z u =
              (QuotientGroup.mk' Z v)⁻¹ * αQ (QuotientGroup.mk' Z v) := hvQ
          _ = QuotientGroup.mk' Z w := by
              change (QuotientGroup.mk' (Subgroup.center G) v)⁻¹ *
                (CFSG.quotientAut α) (QuotientGroup.mk' (Subgroup.center G) v) =
                QuotientGroup.mk' (Subgroup.center G) (v⁻¹ * α v)
              rw [CFSG.quotientAut_mk, ← map_inv, ← map_mul]
      let c : G := w⁻¹ * u
      have hc_mem : c ∈ Z := by
        have hc0 : u⁻¹ * w ∈ Z := (QuotientGroup.eq).mp hq
        dsimp [c]
        simpa using Z.inv_mem hc0
      have hu_eq : u = w * c := by
        dsimp [c]
        group
      have hw_norm : w * α w * α (α w) = 1 := by
        dsimp [w]
        exact norm_inv_mul_aut α hα v
      have hc_norm : c * α c * α (α c) = 1 := by
        have h := norm_mul_of_mem_center α hc_mem w
        rw [← hu_eq, hu, hw_norm, one_mul] at h
        exact h.symm
      have hcommZ : ∀ x y : ↥Z, x * y = y * x := by
        intro x y
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp y.2 (x : G)
      have hcubeZ : Function.Bijective (fun z : ↥Z => z ^ 3) := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          simpa using hcube.1 (congrArg Subtype.val hxy)
        · intro z
          obtain ⟨r, hr⟩ := hcube.2 (z : G)
          have hr' : r ^ 3 = (z : G) := hr
          have hrZ : r ∈ Z :=
            mem_center_of_pow_three_mem_center hcube (by rw [hr']; exact z.2)
          exact ⟨⟨r, hrZ⟩, Subtype.ext hr'⟩
      have hαZ : CFSG.centerAut α ^ 3 = 1 := by
        ext z
        rw [show CFSG.centerAut α ^ 3 =
            CFSG.centerAut α * CFSG.centerAut α * CFSG.centerAut α by
              rw [pow_succ, pow_succ, pow_one]]
        rw [MulAut.mul_apply, MulAut.mul_apply]
        simpa [CFSG.centerAut_coe] using
          apply_three_eq_self_of_pow_three_eq_one α hα (z : G)
      have hcZ_norm : (⟨c, hc_mem⟩ : ↥Z) * CFSG.centerAut α ⟨c, hc_mem⟩ *
          CFSG.centerAut α (CFSG.centerAut α ⟨c, hc_mem⟩) = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_one]
        rw [show ((CFSG.centerAut α ⟨c, hc_mem⟩ : ↥Z) : G) = α c from
          CFSG.centerAut_coe α ⟨c, hc_mem⟩]
        rw [show ((CFSG.centerAut α (CFSG.centerAut α ⟨c, hc_mem⟩) : ↥Z) : G) =
            α ((CFSG.centerAut α ⟨c, hc_mem⟩ : ↥Z) : G) from
          CFSG.centerAut_coe α (CFSG.centerAut α ⟨c, hc_mem⟩)]
        rw [show ((CFSG.centerAut α ⟨c, hc_mem⟩ : ↥Z) : G) = α c from
          CFSG.centerAut_coe α ⟨c, hc_mem⟩]
        exact hc_norm
      obtain ⟨d, hd⟩ := exists_inv_mul_aut_of_mul_comm hcommZ (CFSG.centerAut α)
        hαZ hcubeZ (u := ⟨c, hc_mem⟩) hcZ_norm
      have hdG : c = (d : G)⁻¹ * α (d : G) := by
        have := congrArg Subtype.val hd
        rw [show ((d⁻¹ * CFSG.centerAut α d : ↥Z) : G) =
            (d : G)⁻¹ * α (d : G) by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [show ((CFSG.centerAut α d : ↥Z) : G) = α (d : G) from
            CFSG.centerAut_coe α d]] at this
        exact this
      refine ⟨v * (d : G), ?_⟩
      calc
        u = w * c := hu_eq
        _ = (v⁻¹ * α v) * ((d : G)⁻¹ * α (d : G)) := by
            dsimp only [w]
            rw [hdG]
        _ = (v * (d : G))⁻¹ * α (v * (d : G)) := by
            rw [inv_mul_aut_mul_of_mem_center α d.2 v]

theorem exists_inv_mul_aut_of_norm_one_of_nilpotent
    {G : Type u} [Group G] [Group.IsNilpotent G]
    (α : MulAut G) (hα : α ^ 3 = 1)
    (hcube : Function.Bijective (fun g : G => g ^ 3))
    {u : G} (hu : u * α u * α (α u) = 1) :
    ∃ v : G, u = v⁻¹ * α v :=
  exists_inv_mul_aut_of_nilpotencyClass_le (Group.nilpotencyClass G) G
    (le_refl (Group.nilpotencyClass G)) α hα hcube u hu

end CFSG.GroupTheory

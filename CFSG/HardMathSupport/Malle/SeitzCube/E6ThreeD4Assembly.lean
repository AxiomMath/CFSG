module

public import CFSG.HardMathSupport.Malle.SeitzCube.D4PlaneGen
public import CFSG.LieType.SeitzGeneration.HyperEx

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.LieType.SeitzGeneration

theorem card_sup_of_commute {G : Type*} [Group G] (H K : Subgroup G)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, Commute h k) (hdisj : Disjoint H K) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let φ : H × K →* G := MonoidHom.noncommCoprod H.subtype K.subtype
    (fun h k => hcomm h.1 h.2 k.1 k.2)
  have hr : φ.range = H ⊔ K := by
    have := MonoidHom.noncommCoprod_range H.subtype K.subtype (fun h k => hcomm h.1 h.2 k.1 k.2)
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at this
    exact this
  have hinj : Function.Injective φ := by
    refine (MonoidHom.noncommCoprod_injective H.subtype K.subtype
      (fun h k => hcomm h.1 h.2 k.1 k.2)).2 ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
    simpa only [Subgroup.range_subtype] using hdisj
  have h1 : Nat.card ↥(H ⊔ K) = Nat.card (H × K) := by
    rw [← hr]
    exact (Nat.card_congr (Equiv.ofInjective φ hinj)).symm
  rw [h1, Nat.card_prod]

theorem relIndex_eq_of_card {G : Type*} [Group G] {F cube : Subgroup G} (hle : F ≤ cube) {p : ℕ}
    (hp : 0 < p) (hF : Nat.card F = p ^ 2) (hcube : Nat.card cube = p ^ 3) :
    F.relIndex cube = p := by
  have h1 := Subgroup.card_mul_index (F.subgroupOf cube)
  have h2 : Nat.card (F.subgroupOf cube) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2, hF, hcube] at h1
  have hpos : 0 < p ^ 2 := by positivity
  have : p ^ 2 * F.relIndex cube = p ^ 2 * p := by
    rw [Subgroup.relIndex]
    simpa [pow_succ] using h1
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem le_hyperClosure_of_planeGen {G : Type} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {cube B Y E' : Subgroup G} (hab : CFSG.Open.IsElemAbelian p cube)
    (hcube : Nat.card cube = p ^ 3) (hBle : B ≤ cube) (hB : Nat.card B = p)
    (hBY : Disjoint B Y) (hcent : ∀ y ∈ Y, ∀ b ∈ B, Commute y b)
    (hE'le : E' ≤ cube) (hE'Y : E' ≤ Y) (hE' : Nat.card E' = p ^ 2) (hgen : PlaneGen Y p) :
    Y ≤ hyperClosure p ⊤ cube := by
  have hcomm : ∀ a ∈ cube, ∀ b ∈ cube, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let E'' : Subgroup Y := E'.subgroupOf Y
  have hE''ele : CFSG.IsElementaryAbelian p E'' := by
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      refine Subtype.ext (Subtype.ext ?_)
      exact (hcomm a (hE'le ha) b (hE'le hb)).eq
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      rintro ⟨a, ha⟩
      refine Subtype.ext (Subtype.ext ?_)
      exact hab.2 a (hE'le ha)
  have hE''card : Nat.card E'' = p ^ 2 := by
    rw [← hE']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'Y).toEquiv
  have hgen' := hgen E'' hE''ele hE''card
  have hS : ∀ z : Y, z ∈ Subgroup.closure {k : Y | ∃ x ∈ E'', x ≠ 1 ∧ k * x = x * k} →
      (z : G) ∈ hyperClosure p ⊤ cube := by
    intro z hz
    refine Subgroup.closure_induction (p := fun (z : Y) _ => (z : G) ∈ hyperClosure p ⊤ cube) ?_ ?_ ?_ ?_ hz
    · rintro k ⟨x, hxE, hx1, hk⟩
      have hxE' : (x : G) ∈ E' := hxE
      have hxcube : (x : G) ∈ cube := hE'le hxE'
      have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hord : orderOf (x : G) = p := orderOf_eq_prime (hab.2 _ hxcube) hx1'
      have hzp : Nat.card (Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers]; exact hord
      have hdisj : Disjoint B (Subgroup.zpowers (x : G)) :=
        hBY.mono_right (Subgroup.zpowers_le.2 x.2)
      have hcommBZ : ∀ h ∈ B, ∀ z ∈ Subgroup.zpowers (x : G), Commute h z := by
        intro h hh z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact (hcomm h (hBle hh) (x : G) hxcube).zpow_right n
      have hFcard : Nat.card ↥(B ⊔ Subgroup.zpowers (x : G)) = p ^ 2 := by
        rw [card_sup_of_commute B _ hcommBZ hdisj, hB, hzp]; ring
      have hFle : B ⊔ Subgroup.zpowers (x : G) ≤ cube :=
        sup_le hBle (Subgroup.zpowers_le.2 hxcube)
      have hFcent : B ⊔ Subgroup.zpowers (x : G) ≤ Subgroup.centralizer {(k : G)} := by
        refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (hcent _ k.2 b hb).eq
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact congrArg Subtype.val hk
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, B ⊔ Subgroup.zpowers (x : G), hFle,
        relIndex_eq_of_card hFle hp.out.pos hFcard hcube, fun f hf => ?_⟩
      have := Subgroup.mem_centralizer_iff.1 (hFcent hf) (k : G) rfl
      exact this.symm
    · exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      exact Subgroup.inv_mem _ ha
  intro y hy
  exact hS ⟨y, hy⟩ (hgen' ▸ Subgroup.mem_top _)

end CFSG.HardMathSupport.Malle.SeitzCube

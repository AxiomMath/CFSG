module

public import CFSG.CGT.Timmesfeld75.Config
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_map_of_hom {p : ℕ} {S : Subgroup G} (hS : IsElemAbelian p S)
    (f : G →* H) : IsElemAbelian p (S.map f) := CFSG.Open.IsElemAbelian.map hS _

theorem map_conjSubgroup (f : G →* H) (g : G) (T : Subgroup G) :
    (conjSubgroup g T).map f = conjSubgroup (f g) (T.map f) := by
  ext x
  simp only [Subgroup.mem_map, mem_conjSubgroup]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g * z * g⁻¹, by simpa [mul_assoc] using hz, ?_⟩
    have : x = f g * f z * (f g)⁻¹ := by rw [hzx]; group
    rw [this]
    simp

theorem commute_of_commutator_central_odd {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hZodd : Odd (Nat.card Z)) {x t : G} (hxx : x * x = 1) (htt : t * t = 1)
    (hz : x * t * x * t ∈ Z) : x * t = t * x := by
  set z := x * t * x * t with hzdef
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hzc : x * z = z * x := (Subgroup.mem_center_iff.1 (hZc hz) x)
  have h1 : x * z * x = t * x * t * x := by
    calc x * z * x = x * (x * t * x * t) * x := rfl
      _ = (x * x) * t * x * t * x := by simp only [mul_assoc]
      _ = t * x * t * x := by rw [hxx, one_mul]
  have h2 : x * z * x = z := by
    rw [hzc, mul_assoc, hxx, mul_one]
  have hzz : z * z = 1 := by
    set u := x * t with hu
    have hui : u⁻¹ = t * x := by rw [hu, mul_inv_rev, hxi, hti]
    have hz_u : z = u * u := by simp only [hzdef, hu, mul_assoc]
    have h3 : z = t * x * t * x := by rw [← h2, h1]
    have hz_u' : z = u⁻¹ * u⁻¹ := by rw [h3, hui]; simp only [mul_assoc]
    calc z * z = (u * u) * (u⁻¹ * u⁻¹) := congrArg₂ (· * ·) hz_u hz_u'
      _ = 1 := by group
  have hz1 : z = 1 := by
    have h1' : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
    have h2' : orderOf z ∣ Nat.card Z := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.1
      (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hZodd) h1' h2')
  have : x * t * x * t = 1 := hz1
  calc x * t = x * t * (x * t) * (x * t)⁻¹ := by group
    _ = x * t * (x * t) * (t * x) := by rw [mul_inv_rev, hxi, hti]
    _ = (x * t * x * t) * (t * x) := by simp only [mul_assoc]
    _ = t * x := by rw [this, one_mul]

theorem IsWC.map_quotient_central_odd {T : Subgroup G} (hT : IsWC T) (Z : Subgroup G) [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) (hZodd : Odd (Nat.card Z)) :
    IsWC (T.map (QuotientGroup.mk' Z)) := by
  have hTb := isElemAbelian_map_of_hom hT.1 (QuotientGroup.mk' Z)
  refine ⟨hTb, fun tb htb htb1 => ⟨fun x hx => ?_, fun gb hgb => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact elemAbelian_mul_comm hTb htb hx
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    obtain ⟨t, ht, rfl⟩ := htb
    have ht1 : t ≠ 1 := fun h => htb1 (by rw [h, map_one])
    have hcent : conjSubgroup g T ≤ Subgroup.centralizer ({t} : Set G) := by
      intro x hx
      have hxm : QuotientGroup.mk' Z x ∈
          conjSubgroup (QuotientGroup.mk' Z g) (T.map (QuotientGroup.mk' Z)) := by
        rw [← map_conjSubgroup]
        exact Subgroup.mem_map_of_mem _ hx
      have hxc := Subgroup.mem_centralizer_iff.1 (hgb hxm) (QuotientGroup.mk' Z t)
        (Set.mem_singleton _)
      have hxx : x * x = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hT.1 g) hx
      have htt : t * t = 1 := elemAbelian_mul_self hT.1 ht
      have hz : x * t * x * t ∈ Z := by
        have h1 : QuotientGroup.mk' Z (t * x) = QuotientGroup.mk' Z (x * t) := by
          rw [map_mul, map_mul]; exact hxc
        have h2 := (QuotientGroup.eq (a := t * x) (b := x * t)).1 h1
        have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
        have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
        simpa [mul_inv_rev, hxi, hti, mul_assoc] using h2
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (commute_of_commutator_central_odd hZc hZodd hxx htt hz).symm
    have hconj := (hT.2 t ht ht1).2 g hcent
    rw [show (↑g : G ⧸ Z) = QuotientGroup.mk' Z g from rfl, ← map_conjSubgroup, hconj]

theorem center_sup_commutator_eq_top {K : Type*} [Group K]
    (hs : IsSimpleGroup (K ⧸ Subgroup.center K))
    (hnab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) :
    Subgroup.center K ⊔ commutator K = ⊤ := by
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hnorm : ((commutator K).map π).Normal := Subgroup.Normal.map inferInstance π
    QuotientGroup.mk_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((commutator K).map π) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective b
    have hmem : ⁅k₁, k₂⁆ ∈ commutator K := Subgroup.commutator_mem_commutator trivial trivial
    have h1 : π ⁅k₁, k₂⁆ ∈ (commutator K).map π := Subgroup.mem_map_of_mem _ hmem
    rw [h, Subgroup.mem_bot, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  · rw [eq_top_iff]
    intro k _
    have hk : π k ∈ (commutator K).map π := by rw [h]; trivial
    obtain ⟨c, hc, hck⟩ := hk
    have hzc : c⁻¹ * k ∈ Subgroup.center K := (QuotientGroup.eq).1 hck
    have : k = c * (c⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hzc)

theorem commutator_eq_top_of_odd_center {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsElemAbelian 2 T) (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (hZ : Odd (Nat.card (Subgroup.center K))) (hKc : Subgroup.center K ⊔ commutator K = ⊤) :
    commutator K = ⊤ := by
  have hsq : ∀ k : K, (Abelianization.of k) ^ 2 = 1 := by
    intro k
    have hk : k ∈ Subgroup.normalClosure (T : Set K) := by rw [hK]; trivial
    refine Subgroup.closure_induction (p := fun k _ => (Abelianization.of k) ^ 2 = 1)
      ?_ ?_ ?_ ?_ hk
    · intro x hx
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
      have : Abelianization.of (c * a * c⁻¹) = Abelianization.of a := by
        rw [map_mul, map_mul, map_inv, mul_comm (Abelianization.of c), mul_assoc, mul_inv_cancel,
          mul_one]
      rw [this, ← map_pow, hT.2 a ha, map_one]
    · simp
    · intro x y _ _ hx hy
      rw [map_mul, mul_pow, hx, hy, one_mul]
    · intro x _ hx
      rw [map_inv, inv_pow, hx, inv_one]
  rw [eq_top_iff]
  intro k _
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  have hk : k ∈ Subgroup.center K ⊔ commutator K := by rw [hKc]; trivial
  obtain ⟨z, hz, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hk
  have hc1 : Abelianization.of c = 1 := by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]; exact hc
  rw [map_mul, hc1, mul_one]
  have h1 : orderOf (Abelianization.of z) ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq z)
  have h2 : orderOf (Abelianization.of z) ∣ Nat.card (Subgroup.center K) := by
    have h3 : orderOf z ∣ Nat.card (Subgroup.center K) := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center K)
      rwa [Subgroup.orderOf_mk] at this
    exact (orderOf_map_dvd Abelianization.of z).trans h3
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hZ) h1 h2)

end CFSG.CGT.Timmesfeld75

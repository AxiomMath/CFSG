module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg
public import CFSG.ClassicalInvolution.Sp62Rec.EOdd

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

section Helpers

variable {K : Type*} [Group K] [Finite K]

theorem sup_eq_top_of_coprime_index (N : Subgroup K) [N.Normal] (hq : IsPGroup 2 (K ⧸ N))
    (S : Subgroup K) (hS : Nat.Coprime S.index 2) : S ⊔ N = ⊤ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hq
  have hM1 : (S ⊔ N).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_left
  have hM2 : (S ⊔ N).index ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_of_le le_sup_right
  have hMcop : Nat.Coprime (S ⊔ N).index 2 := Nat.Coprime.coprime_dvd_left hM1 hS
  exact Subgroup.index_eq_one.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hMcop) hM2)

theorem sq_eq_one_of_mem_zpowers {G : Type*} [Group G] {e : G} (he : e * e = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers e) : x ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have he2 : e ^ 2 = 1 := by rw [pow_two]; exact he
  rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, he2, one_zpow]

end Helpers

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G}

theorem E8ZPkg.centralizer_eq_B (P : E8ZPkg z e E B T A X)
    (φ : ↥B ≃* ↥Hhat) (hφE : (E.subgroupOf B).map φ.toMonoidHom = E0.subgroupOf Hhat)
    (hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e) (he2 : e * e = 1)
    (V : Subgroup ↥E0) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (↥E0 ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V, (∀ (x : ↥E0) (v : V),
      f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1) :
    Subgroup.centralizer ({e} : Set G) = B := by
  set Ce : Subgroup G := Subgroup.centralizer ({e} : Set G)
  have hEC : E ≤ Ce := P.E_le_B.trans P.B_le
  have hTC : (T : Subgroup G) ≤ Ce := P.T_le.trans P.B_le
  haveI hEn : (E.subgroupOf Ce).Normal :=
    (Subgroup.normal_subgroupOf_iff hEC).2 fun h k hh hk => by
      have h1 : k * h * k⁻¹ ∈ E.map (MulAut.conj k).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hh
      rwa [P.E_normal k hk] at h1
  have hE0H : E0 ≤ Hhat := Subgroup.commutator_le_of_le le_rfl le_rfl
  let θE : ↥E0 ≃* ↥E :=
    (Subgroup.subgroupOfEquivOfLe hE0H).symm.trans
      ((MulEquiv.subgroupCongr hφE).symm.trans
        ((MulEquiv.subgroupMap φ (E.subgroupOf B)).symm.trans
          (Subgroup.subgroupOfEquivOfLe P.E_le_B)))
  let θ : ↥E0 ≃* ↥(E.subgroupOf Ce) := θE.trans (Subgroup.subgroupOfEquivOfLe hEC).symm
  have hC : IsPGroup 2 (Subgroup.centralizer ((E.subgroupOf Ce : Subgroup ↥Ce) : Set ↥Ce)) := by
    intro y
    refine ⟨1, ?_⟩
    have hyG : ((y : ↥Ce) : G) ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hy := Subgroup.mem_centralizer_iff.1 y.2 ⟨a, hEC ha⟩
        (show (⟨a, hEC ha⟩ : ↥Ce) ∈ E.subgroupOf Ce from Subgroup.mem_subgroupOf.2 ha)
      exact congrArg Subtype.val hy
    rw [hCE] at hyG
    have hsq := sq_eq_one_of_mem_zpowers he2 hyG
    apply Subtype.ext
    apply Subtype.ext
    simpa using hsq
  have hq : IsPGroup 2 (↥Ce ⧸ E.subgroupOf Ce) :=
    isPGroup_two_quotient (E.subgroupOf Ce) θ V hV hA6 hcomm hC
  have hTcop : Nat.Coprime (T : Subgroup G).index 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Sylow.not_dvd_index T)).symm
  have hTdvd : ((T : Subgroup G).subgroupOf Ce).index ∣ (T : Subgroup G).index :=
    Dvd.intro _ (Subgroup.relIndex_mul_index hTC)
  have hTodd : Nat.Coprime ((T : Subgroup G).subgroupOf Ce).index 2 :=
    Nat.Coprime.coprime_dvd_left hTdvd hTcop
  have hTE : (T : Subgroup G).subgroupOf Ce ⊔ E.subgroupOf Ce = ⊤ :=
    sup_eq_top_of_coprime_index (E.subgroupOf Ce) hq _ hTodd
  have hCB : Ce ≤ B := by
    intro g hg
    have hgM : (⟨g, hg⟩ : ↥Ce) ∈ (T : Subgroup G).subgroupOf Ce ⊔ E.subgroupOf Ce := by
      rw [hTE]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, n, hn, hsn⟩ := Subgroup.mem_sup_of_normal_right.1 hgM
    have hsT : (s : G) ∈ (T : Subgroup G) := Subgroup.mem_subgroupOf.1 hs
    have hnE : (n : G) ∈ E := Subgroup.mem_subgroupOf.1 hn
    have hg' : g = (s : G) * (n : G) := (congrArg Subtype.val hsn).symm
    rw [hg']
    exact B.mul_mem (P.T_le hsT) (P.E_le_B hnE)
  exact le_antisymm hCB P.B_le

end CFSG.ClassicalInvolution.Sp62Rec

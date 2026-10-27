module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LieType.SteinbergBR

variable {G H : Type*} [Group G] [Group H]

theorem perfectResidual_map_equiv (e : G ≃* H) :
    (CFSG.perfectResidual G).map e.toMonoidHom = CFSG.perfectResidual H := by
  rw [CFSG.perfectResidual, CFSG.perfectResidual, Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

theorem map_sSup_of_equiv (e : G ≃* H) {SG : Set (Subgroup G)} {SH : Set (Subgroup H)}
    (h1 : ∀ K ∈ SG, K.map e.toMonoidHom ∈ SH) (h2 : ∀ K ∈ SH, K.comap e.toMonoidHom ∈ SG) :
    (sSup SG).map e.toMonoidHom = sSup SH := by
  rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup]
  refine le_antisymm (iSup₂_le fun K hK => le_sSup (h1 K hK)) (sSup_le fun K hK => ?_)
  calc K = (K.comap e.toMonoidHom).map e.toMonoidHom :=
        (Subgroup.map_comap_eq_self_of_surjective e.surjective K).symm
    _ ≤ ⨆ L ∈ SG, L.map e.toMonoidHom := le_iSup₂_of_le (K.comap e.toMonoidHom) (h2 K hK) le_rfl

theorem isSolvable_map (f : G →* H) (K : Subgroup G) [Group.IsSolvable K] :
    Group.IsSolvable (K.map f) :=
  Group.isSolvable_of_surjective (f.subgroupMap_surjective K)

theorem solvableRadical_map_equiv (e : G ≃* H) :
    (CFSG.solvableRadical G).map e.toMonoidHom = CFSG.solvableRadical H := by
  refine map_sSup_of_equiv e (fun K hK => ⟨hK.1.map _ e.surjective, ?_⟩)
    fun K hK => ⟨hK.1.comap _, ?_⟩
  · have := hK.2
    exact isSolvable_map _ K
  · have := hK.2
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact isSolvable_map _ K

theorem pCore_map_equiv (p : ℕ) (e : G ≃* H) :
    (CFSG.pCore p G).map e.toMonoidHom = CFSG.pCore p H := by
  refine map_sSup_of_equiv e (fun K hK => ⟨hK.1.map _ e.surjective, hK.2.map _⟩)
    fun K hK => ⟨hK.1.comap _, ?_⟩
  rw [Subgroup.comap_equiv_eq_map_symm']
  exact hK.2.map _

instance solvableRadical_normal (G : Type*) [Group G] : (CFSG.solvableRadical G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem not_isSolvable_of_isPerfect [Nontrivial G] [Group.IsPerfect G] : ¬ Group.IsSolvable G := by
  intro hs
  obtain ⟨n, hn⟩ := hs.solvable
  rw [Group.IsPerfect.derivedSeries_eq_top] at hn
  exact top_ne_bot hn

theorem ordProj_prime_pow_mul {p : ℕ} (hp : p.Prime) (k : ℕ) {m : ℕ} (hm : ¬ p ∣ m) :
    ordProj[p] (p ^ k * m) = p ^ k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

end CFSG.LieType.SteinbergBR

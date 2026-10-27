module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G}

private theorem ceTheta_isE64_map {H K : Type} [Group H] [Group K] {X : Subgroup H}
    (hX : IsE64 X) (f : H →* K) (hf : Function.Injective f) : IsE64 (X.map f) := by
  obtain ⟨hc, hs, hcard⟩ := hX
  unfold IsE64
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hc a' ha' b' hb']
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul, hs a' ha', map_one]
  · rw [Subgroup.card_map_of_injective hf, hcard]

private theorem ceTheta_isE64_subgroupOf {A K : Subgroup G} (h : A ≤ K) (hA : IsE64 A) :
    IsE64 (A.subgroupOf K) := by
  obtain ⟨hc, hs, hcard⟩ := hA
  unfold IsE64
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hc _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  · intro a ha
    exact Subtype.ext (hs _ (Subgroup.mem_subgroupOf.mp ha))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, hcard]

private theorem ceTheta_map_trans {M N P : Type} [Group M] [Group N] [Group P]
    (f : M ≃* N) (g : N ≃* P) (X : Subgroup M) :
    X.map (f.trans g).toMonoidHom = (X.map f.toMonoidHom).map g.toMonoidHom := by
  have h : (f.trans g).toMonoidHom = g.toMonoidHom.comp f.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [h, Subgroup.map_map]

private theorem ceTheta_commutator_conj {K : Subgroup G} (g : K) :
    ((⁅K, K⁆ : Subgroup G).subgroupOf K).map (MulAut.conj g).toMonoidHom =
      (⁅K, K⁆ : Subgroup G).subgroupOf K := by
  have htop : (⊤ : Subgroup K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : Subgroup.map K.subtype ⁅(⊤ : Subgroup K), ⊤⁆ = ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, htop]
  have hsub : (⁅K, K⁆ : Subgroup G).subgroupOf K = ⁅(⊤ : Subgroup K), ⊤⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K) _
  rw [hsub, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective]

theorem E8ZPkg.exists_theta (P : E8ZPkg z e E B T A X)
    (hCeB : Subgroup.centralizer ({e} : Set G) = B)
    (φ : ↥B ≃* ↥Hhat) (hφE : (E.subgroupOf B).map φ.toMonoidHom = E0.subgroupOf Hhat)
    (hφe : φ ⟨e, P.E_le_B P.e_mem⟩ = ⟨alpha, alpha_mem_Hhat⟩)
    (A0 : Subgroup (StatedSp 3 (ZMod 2)))
    (hA0 : ∀ A' : Subgroup (StatedSp 3 (ZMod 2)), A' ≤ S0 → IsE64 A' → A' = A0)
    (hS0 : Nat.card S0 = 512) (hH : Nat.card Hhat = 23040)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2)))) :
    ∃ θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat,
      θ ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = ⟨alpha, alpha_mem_Hhat⟩ ∧
      ((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
        S0.subgroupOf Hhat ∧
      (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom = A0.subgroupOf Hhat ∧
      (E.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom = E0.subgroupOf Hhat := by
  subst hCeB
  have hTCe : (T : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := P.T_le
  have hAle : (A : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := P.A_le.trans hTCe
  haveI : Finite ↥Hhat := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  haveI : Finite (Sylow 2 ↥Hhat) :=
    Finite.of_injective (fun Q : Sylow 2 ↥Hhat => (Q : Set ↥Hhat)) SetLike.coe_injective
  obtain ⟨SQ, hSQ⟩ : ∃ SQ : Sylow 2 ↥Hhat,
      (SQ : Subgroup ↥Hhat) =
        ((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))).map φ.toMonoidHom :=
    ⟨Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective (T.subtype hTCe), rfl⟩
  have hcardS : Nat.card ↥(S0.subgroupOf Hhat) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, hS0]
  have hidx : (S0.subgroupOf Hhat).index = 45 := by
    have h1 := Subgroup.card_mul_index (S0.subgroupOf Hhat)
    rw [hcardS, hH] at h1
    omega
  have hP2 : ¬ 2 ∣ (S0.subgroupOf Hhat).index := by
    rw [hidx]
    norm_num
  have hP1 : IsPGroup 2 (S0.subgroupOf Hhat) :=
    IsPGroup.of_card (n := 9) (hcardS.trans (by norm_num))
  obtain ⟨SS, hSS⟩ : ∃ SS : Sylow 2 ↥Hhat, (SS : Subgroup ↥Hhat) = S0.subgroupOf Hhat :=
    ⟨hP1.toSylow hP2, rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Hhat SQ SS
  have hgSQ : (SQ : Subgroup ↥Hhat).map (MulAut.conj g).toMonoidHom = S0.subgroupOf Hhat := by
    rw [← hSS]
    exact congrArg (fun Q : Sylow 2 ↥Hhat => (Q : Subgroup ↥Hhat)) hg
  have hθe : (φ.trans (MulAut.conj g)) ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ =
      ⟨alpha, alpha_mem_Hhat⟩ := by
    rw [MulEquiv.trans_apply, hφe]
    apply Subtype.ext
    show (g : StatedSp 3 (ZMod 2)) * alpha * (g : StatedSp 3 (ZMod 2))⁻¹ = alpha
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hα g.2)
  have hTθ : ((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))).map
      (φ.trans (MulAut.conj g)).toMonoidHom = S0.subgroupOf Hhat := by
    rw [ceTheta_map_trans, ← hSQ]
    exact hgSQ
  have hAθ : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
      (φ.trans (MulAut.conj g)).toMonoidHom = A0.subgroupOf Hhat := by
    have hAle' : A.subgroupOf (Subgroup.centralizer ({e} : Set G)) ≤
        (T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G)) :=
      Subgroup.subgroupOf_mono _ P.A_le
    have hAθle : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        (φ.trans (MulAut.conj g)).toMonoidHom ≤ S0.subgroupOf Hhat := by
      rw [← hTθ]
      exact Subgroup.map_mono hAle'
    have hAe : IsE64 (A.subgroupOf (Subgroup.centralizer ({e} : Set G))) :=
      ceTheta_isE64_subgroupOf hAle P.e64
    have hAθ64 : IsE64 ((A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        (φ.trans (MulAut.conj g)).toMonoidHom) :=
      ceTheta_isE64_map hAe (φ.trans (MulAut.conj g)).toMonoidHom (φ.trans (MulAut.conj g)).injective
    have hA'64 : IsE64 (((A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        (φ.trans (MulAut.conj g)).toMonoidHom).map Hhat.subtype) :=
      ceTheta_isE64_map hAθ64 Hhat.subtype (Subgroup.subtype_injective Hhat)
    have hA'le : (((A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        (φ.trans (MulAut.conj g)).toMonoidHom).map Hhat.subtype) ≤ S0 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_subgroupOf.mp (hAθle hy)
    have hA'eq := hA0 _ hA'le hA'64
    rw [← hA'eq]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective Hhat) _).symm
  have hE : (E.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
      (φ.trans (MulAut.conj g)).toMonoidHom = E0.subgroupOf Hhat := by
    rw [ceTheta_map_trans, hφE]
    exact ceTheta_commutator_conj g
  exact ⟨φ.trans (MulAut.conj g), hθe, hTθ, hAθ, hE⟩

end CFSG.ClassicalInvolution.Sp62Rec

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co15Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem isQuasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := hA
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

theorem glaPComponent_subgroupOf {G : Type} [Group G] (P : Subgroup G) [Finite ↥P] {p : ℕ}
    (hp : p.Prime) (S : Set ↥P) {J : Subgroup G} (hJP : J ≤ P)
    (hJC : ∀ l ∈ J, ∀ s ∈ S, l * (s : G) = (s : G) * l)
    (hJn : ∀ g ∈ P, (∀ s ∈ S, g * (s : G) = (s : G) * g) → ∀ l ∈ J, g * l * g⁻¹ ∈ J)
    (hq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card ↥J) :
    GLAPComponent p (Subgroup.centralizer S) (J.subgroupOf P) := by
  have eJ : ↥(J.subgroupOf P) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJP
  have hle : J.subgroupOf P ≤ Subgroup.centralizer S := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subtype.ext (hJC _ (Subgroup.mem_subgroupOf.1 hl) s hs).symm
  refine CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp
    (isQuasisimple_of_equiv eJ.symm hq) (by rw [Nat.card_congr eJ.toEquiv]; exact hpJ) hle ?_
  refine ⟨fun e he g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at he ⊢
  have hg : ∀ s ∈ S, ((g : ↥P) : G) * (s : G) = (s : G) * ((g : ↥P) : G) := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 g.2 s hs).symm
  rw [Subgroup.mem_subgroupOf]
  exact hJn _ (g : ↥P).2 hg _ he

theorem le_of_comm_of_card2 {G : Type} [Group G] [Finite G] {i m0 m1 : ℕ} {Q E A : Subgroup G}
    (hEQ : E ≤ Q) (hidx : E.relIndex Q = i) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcen : ∀ r ∈ Q, r ∉ E → Nat.card ↥(E ⊓ Subgroup.centralizer ({r} : Set G)) ≤ m1)
    {r0 : G} (hr0 : r0 ∈ Q) (hr0c : Nat.card ↥(E ⊓ Subgroup.centralizer ({r0} : Set G)) ≤ m0)
    (hAQ : A ≤ Q) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h1 : (i - 1) * m1 < Nat.card A)
    (h0 : i * m0 < Nat.card A) : A ≤ E := by
  intro r hr
  by_contra hnot
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K h => by
    have := Subgroup.relIndex_mul_card H K
    rw [h, zero_mul] at this
    exact (Nat.card_pos (α := ↥K)).ne' this.symm
  have hi : i ≠ 0 := by rw [← hidx]; exact hne _ _
  have hle : E ⊓ A ≤ E ⊓ Subgroup.centralizer ({r} : Set G) := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, Subgroup.mem_centralizer_singleton_iff.2
      (hA x (Subgroup.mem_inf.1 hx).2 r hr)⟩
  have hB1 : Nat.card ↥(E ⊓ A) ≤ m1 :=
    (Subgroup.card_le_of_le hle).trans (hcen r (hAQ hr) hnot)
  have hiA : E.relIndex A ≤ i := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right hAQ (by rw [hidx]; exact hi)
  have h3 := Subgroup.relIndex_mul_card E A
  have hiA' : E.relIndex A = i := by
    by_contra hne
    have hlt : E.relIndex A ≤ i - 1 := by omega
    have : Nat.card A ≤ (i - 1) * m1 := by
      rw [← h3]
      exact Nat.mul_le_mul hlt hB1
    omega
  set K : Subgroup G := Q ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) with hK
  have hAK : A ≤ K := fun a ha => Subgroup.mem_inf.2 ⟨hAQ ha,
    Subgroup.mem_centralizer_iff.2 fun b hb => hA b (Subgroup.mem_inf.1 hb).2 a ha⟩
  have hEK : E ≤ K := fun a ha => Subgroup.mem_inf.2 ⟨hEQ ha,
    Subgroup.mem_centralizer_iff.2 fun b hb => hEab b (Subgroup.mem_inf.1 hb).1 a ha⟩
  have hiK : i ≤ E.relIndex K := by
    rw [← hiA']
    exact Subgroup.relIndex_le_of_le_right hAK (hne _ _)
  have hKQ : K = Q := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    have hQ := Subgroup.relIndex_mul_card E Q
    have hK' := Subgroup.relIndex_mul_card E K
    rw [inf_eq_left.2 hEQ, hidx] at hQ
    rw [inf_eq_left.2 hEK] at hK'
    rw [← hQ, ← hK']
    exact Nat.mul_le_mul_right _ hiK
  have hr0K : r0 ∈ K := hKQ ▸ hr0
  have hle0 : E ⊓ A ≤ E ⊓ Subgroup.centralizer ({r0} : Set G) := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr0K).2 x hx)⟩
  have hB0 : Nat.card ↥(E ⊓ A) ≤ m0 := (Subgroup.card_le_of_le hle0).trans hr0c
  have : Nat.card A ≤ i * m0 := by
    rw [← h3, hiA']
    exact Nat.mul_le_mul_left _ hB0
  omega

theorem kd264RowData_of_uniq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q E F1 F2 : Subgroup G} (hQ : Nat.card Q = p ^ (Nat.card G).factorization p)
    (hE : IsElemAbelian p E)
    (huniq : ∀ A : Subgroup G, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card E ≤ Nat.card A → A ≤ E)
    (hF1 : F1 ≤ E) (hF1c : Nat.card F1 = p)
    (hJ1 : ∃ J : Subgroup G, GLAPComponent p (Subgroup.centralizer (F1 : Set G)) J)
    (hF2 : F2 ≤ E) (hF2c : Nat.card F2 = p ^ 2)
    (hJ2 : ∃ J : Subgroup G, GLAPComponent p (Subgroup.centralizer (F2 : Set G)) J) :
    KD264RowData p G := by
  intro A hA hmax k hk1 hk2 _
  have hEA : Nat.card E ≤ Nat.card A := hmax _ hE
  obtain ⟨g, hg⟩ := exists_conj_le_of_full hQ (isPGroup_of_isElemAbelian hA)
  have hA'el : IsElemAbelian p (A.map (MulAut.conj g).toMonoidHom) := hA.map _
  have hA'card : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hA'le : A.map (MulAut.conj g).toMonoidHom ≤ E := huniq _ hg
    (fun x hx y hy => congrArg Subtype.val (hA'el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (by rw [hA'card]; exact hEA)
  have hA'eq : A.map (MulAut.conj g).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hA'le (by rw [hA'card]; exact hEA)
  obtain ⟨F0, hF0, hF0c, J, hJ⟩ : ∃ F0 : Subgroup G, F0 ≤ E ∧ Nat.card F0 = p ^ k ∧
      ∃ J : Subgroup G, GLAPComponent p (Subgroup.centralizer (F0 : Set G)) J := by
    interval_cases k
    · exact ⟨F1, hF1, by rw [hF1c, pow_one], hJ1⟩
    · exact ⟨F2, hF2, hF2c, hJ2⟩
  refine ⟨F0.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, J.map (MulAut.conj g⁻¹).toMonoidHom, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxA' : x ∈ A.map (MulAut.conj g).toMonoidHom := hA'eq ▸ hF0 hx
    obtain ⟨a, ha, rfl⟩ := hxA'
    show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ ∈ A
    have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
    rw [e]
    exact ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hF0c]
  · rw [← HN3.map_conj_centralizer_sub]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv (Fact.out : p.Prime)
      (MulAut.conj g⁻¹) hJ

theorem card_closure_pair_subtype {G : Type} [Group G] (P : Subgroup G) (a b : ↥P) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set ↥P)) =
      Nat.card ↥(Subgroup.closure ({(a : G), (b : G)} : Set G)) := by
  rw [← Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective,
    MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_conj_closure_pair {T : Type*} [Group T] (g a b : T) :
    (Subgroup.closure ({a, b} : Set T)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set T) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem conj_plane_facts {T : Type} [Group T] [Finite T] {E : Subgroup T}
    (hE : IsElemAbelian 3 E) (n x z : T) (hx : n⁻¹ * x * n ∈ E) (hz : n⁻¹ * z * n ∈ E)
    (hcard : Nat.card ↥(Subgroup.closure ({x, z} : Set T)) = 9) :
    orderOf (n⁻¹ * x * n) = 3 ∧ Subgroup.closure ({n⁻¹ * x * n, n⁻¹ * z * n} : Set T) ≤ E ∧
      Nat.card ↥(Subgroup.closure ({n⁻¹ * x * n, n⁻¹ * z * n} : Set T)) = 3 ^ 2 := by
  have hc : ∀ y : T, n⁻¹ * y * n = n⁻¹ * y * n⁻¹⁻¹ := fun y => by rw [inv_inv]
  have hz3 : z ^ 3 = 1 := by
    have h := hE.2 _ hz
    rw [hc, conj_pow] at h
    calc z ^ 3 = n * (n⁻¹ * z ^ 3 * n⁻¹⁻¹) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hx1 : n⁻¹ * x * n ≠ 1 := by
    intro h
    have hr : x = 1 := by
      calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [hr] at hcard
    have hle : Subgroup.closure ({(1 : T), z} : Set T) ≤ Subgroup.zpowers z := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have h3 : Nat.card (Subgroup.zpowers z) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
    have := (Subgroup.card_le_of_le hle).trans h3
    omega
  refine ⟨orderOf_eq_prime (hE.2 _ hx) hx1, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hz
  · rw [hc x, hc z, ← map_conj_closure_pair,
      Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hcard]
    norm_num

theorem comps_conj {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (n xA zA : T)
    {K : Subgroup T}
    (hK1 : GLAPComponent p (Subgroup.centralizer ({xA} : Set T)) K)
    (hK2 : GLAPComponent p (Subgroup.centralizer ({xA, zA} : Set T)) K) :
    (∃ J : Subgroup T, GLAPComponent p
      (Subgroup.centralizer ((Subgroup.zpowers (n⁻¹ * xA * n) : Subgroup T) : Set T)) J) ∧
    ∃ J : Subgroup T, GLAPComponent p (Subgroup.centralizer
      ((Subgroup.closure ({n⁻¹ * xA * n, n⁻¹ * zA * n} : Set T) : Subgroup T) : Set T)) J := by
  refine ⟨⟨K.map (MulAut.conj n⁻¹).toMonoidHom, ?_⟩, ⟨K.map (MulAut.conj n⁻¹).toMonoidHom, ?_⟩⟩
  · rw [Seven.centralizer_zpowers_eq, show n⁻¹ * xA * n = n⁻¹ * xA * n⁻¹⁻¹ by rw [inv_inv],
      ← Seven.map_conj_centralizer]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj n⁻¹) hK1
  · have e : Subgroup.closure ({n⁻¹ * xA * n, n⁻¹ * zA * n} : Set T) =
        (Subgroup.closure ({xA, zA} : Set T)).map (MulAut.conj n⁻¹).toMonoidHom := by
      rw [map_conj_closure_pair, inv_inv]
    rw [e, ← HN3.map_conj_centralizer_sub, Subgroup.centralizer_closure]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj n⁻¹) hK2

theorem kd264RowData_three_of_plane {T : Type} [Group T] [Finite T] {Q E : Subgroup T}
    (hQ : Nat.card Q = 3 ^ (Nat.card T).factorization 3) (hE : IsElemAbelian 3 E)
    (huniq : ∀ A : Subgroup T, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card E ≤ Nat.card A → A ≤ E)
    (n x z : T) (hx : n⁻¹ * x * n ∈ E) (hz : n⁻¹ * z * n ∈ E)
    (hcard : Nat.card ↥(Subgroup.closure ({x, z} : Set T)) = 9) {K : Subgroup T}
    (hK1 : GLAPComponent 3 (Subgroup.centralizer ({x} : Set T)) K)
    (hK2 : GLAPComponent 3 (Subgroup.centralizer ({x, z} : Set T)) K) : KD264RowData 3 T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ho, hF2, hF2c⟩ := conj_plane_facts hE n x z hx hz hcard
  obtain ⟨hJ1, hJ2⟩ := comps_conj Nat.prime_three n x z hK1 hK2
  exact kd264RowData_of_uniq hQ hE huniq (Subgroup.zpowers_le.2 hx)
    (by rw [Nat.card_zpowers, ho]) hJ1 hF2 hF2c hJ2

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15

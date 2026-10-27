module

public import CFSG.LieType.Chevalley.TwistHolds
public import CFSG.LieType.Chevalley.OrbitGroups

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] noncomputable def twistDerived : Subgroup (adjointGroup t.tag K) :=
  (commutator (twistFixed t K σ)).map (twistFixed t K σ).subtype

variable {t K σ}

theorem commutator_mem_twistDerived {g h : adjointGroup t.tag K} (hg : g ∈ twistFixed t K σ)
    (hh : h ∈ twistFixed t K σ) : g * h * g⁻¹ * h⁻¹ ∈ twistDerived t K σ := by
  have hc := Subgroup.commutator_mem_commutator (g₁ := (⟨g, hg⟩ : twistFixed t K σ))
    (g₂ := ⟨h, hh⟩) (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [← commutator_def, commutatorElement_def] at hc
  refine ⟨_, hc, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]

theorem conj_mem_twistDerived {g x : adjointGroup t.tag K} (hg : g ∈ twistFixed t K σ)
    (hx : x ∈ twistDerived t K σ) : g * x * g⁻¹ ∈ twistDerived t K σ := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (instNormalCommutator _).conj_mem y hy _, by simp⟩

theorem xElement_mem_twistFixed {i : Fin t.tag.rank} (hi : t.perm i = i) {c : K}
    (hc : σ c = c) : xElement i c ∈ twistFixed t K σ := by
  rw [mem_twistFixed, twistC_xElement, hi, hc]

theorem nrep_mem_twistFixed' {w : WeylGroup t.tag} (hw : weylTwist t w = w) :
    nrep t.tag K w ∈ twistFixed t K σ := by
  rw [mem_twistFixed, twistC_nrep, hw]

theorem ringHom_eq_of_sign {ε : K} (hε : ε = 1 ∨ ε = -1) : σ ε = ε := by
  rcases hε with rfl | rfl
  · exact map_one σ
  · rw [map_neg, map_one]

section E6

theorem e6_simple_three_smul :
    simple TwistTag.E6.tag ⟨3, by decide⟩ • simpleRoot TwistTag.E6.tag ⟨1, by decide⟩ =
      rootAt TwistTag.E6.tag 9 (by decide) := by
  apply Subtype.ext
  rw [coe_smul_root, simple_smul]
  change reflect .E6 (3 : Fin 6) (Pi.single (1 : Fin 6) 1) = e6Certificate.root 9
  decide +kernel

theorem e6_simple_one_smul :
    simple TwistTag.E6.tag ⟨1, by decide⟩ • simpleRoot TwistTag.E6.tag ⟨3, by decide⟩ =
      rootAt TwistTag.E6.tag 9 (by decide) := by
  apply Subtype.ext
  rw [coe_smul_root, simple_smul]
  change reflect .E6 (1 : Fin 6) (Pi.single (3 : Fin 6) 1) = e6Certificate.root 9
  decide +kernel

theorem e6_commutator (s u : K) :
    xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) s * xElement ⟨3, by decide⟩ u *
        (xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) s)⁻¹ *
        (xElement (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) u)⁻¹ =
      (rootOperatorFamily TwistTag.E6.tag).eltElement (rootAt TwistTag.E6.tag 9 (by decide))
        (-(s * u)) := by
  have h := commutator_eltElement_of_repCheck (τ := TwistTag.E6.tag) (K := K) e6_allValid
    (a := 1) (b := 3) (g := 9) (C := -1) (by decide +kernel) (by decide)
    (rootPos_simpleRoot (τ := TwistTag.E6.tag) ⟨1, by decide⟩)
    (rootPos_simpleRoot (τ := TwistTag.E6.tag) ⟨3, by decide⟩) s u
  rw [eltElement_simpleRoot, eltElement_simpleRoot] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem e6_eltElement_nine_mem {c : K} (hc : σ c = c) :
    (rootOperatorFamily TwistTag.E6.tag).eltElement (rootAt TwistTag.E6.tag 9 (by decide)) c ∈
      twistDerived .E6 K σ := by
  have h := e6_commutator (K := K) (-c) 1
  rw [show -(-c * 1) = c by ring] at h
  rw [← h]
  exact commutator_mem_twistDerived (xElement_mem_twistFixed (by decide) (by rw [map_neg, hc]))
    (xElement_mem_twistFixed (by decide) (map_one σ))

theorem mem_twistDerived_of_conj {w : WeylGroup t.tag} (hw : weylTwist t w = w)
    {α γ : Root t.tag} (hwα : w • α = γ)
    (hγ : ∀ c : K, σ c = c → (rootOperatorFamily t.tag).eltElement γ c ∈ twistDerived t K σ)
    {c : K} (hc : σ c = c) :
    (rootOperatorFamily t.tag).eltElement α c ∈ twistDerived t K σ := by
  obtain ⟨ε, hε, h⟩ := exists_conj_nrep (K := K) w α
  rw [hwα] at h
  have hn : (nrep t.tag K w)⁻¹ ∈ twistFixed t K σ := inv_mem (nrep_mem_twistFixed' hw)
  have hmem := conj_mem_twistDerived hn (hγ (ε * c) (by rw [map_mul, ringHom_eq_of_sign hε, hc]))
  rw [← h c, inv_inv] at hmem
  simpa [mul_assoc] using hmem

theorem e6_xElement_one_mem {c : K} (hc : σ c = c) :
    xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) c ∈ twistDerived .E6 K σ := by
  rw [← eltElement_simpleRoot]
  refine mem_twistDerived_of_conj (w := simple TwistTag.E6.tag ⟨3, by decide⟩) ?_
    e6_simple_three_smul (fun c hc => e6_eltElement_nine_mem hc) hc
  rw [weylTwist_simple]
  rfl

theorem e6_xElement_three_mem {c : K} (hc : σ c = c) :
    xElement (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) c ∈ twistDerived .E6 K σ := by
  rw [← eltElement_simpleRoot]
  refine mem_twistDerived_of_conj (w := simple TwistTag.E6.tag ⟨1, by decide⟩) ?_
    e6_simple_one_smul (fun c hc => e6_eltElement_nine_mem hc) hc
  rw [weylTwist_simple]
  rfl

end E6

section D4

theorem weylTwist_wordProd_eq {ω : List (Fin t.tag.rank)}
    (h : ∀ k : Fin t.tag.rank, (ω.map t.perm).foldr (reflect t.tag) (Pi.single k 1) =
      ω.foldr (reflect t.tag) (Pi.single k 1)) :
    weylTwist t ((coxeterSystem t.tag).wordProd ω) = (coxeterSystem t.tag).wordProd ω := by
  rw [weylTwist_wordProd]
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul, h k]

theorem d4_w_smul :
    (coxeterSystem TwistTag.D4.tag).wordProd (twistOrbitWord .D4 ⟨0, by decide⟩) •
        simpleRoot TwistTag.D4.tag ⟨2, by decide⟩ = rootAt TwistTag.D4.tag 19 (by decide) := by
  apply Subtype.ext
  rw [coe_smul_root, wordProd_smul]
  change ([0, 1, 3] : List (Fin 4)).foldr (reflect .D4)
    (Pi.single (2 : Fin 4) 1) = d4Certificate.root 19
  decide +kernel

theorem d4_w'_smul :
    (coxeterSystem TwistTag.D4.tag).wordProd
        (twistOrbitWord .D4 ⟨2, by decide⟩ ++ twistOrbitWord .D4 ⟨0, by decide⟩) •
        simpleRoot TwistTag.D4.tag ⟨2, by decide⟩ = rootAt TwistTag.D4.tag 22 (by decide) := by
  apply Subtype.ext
  rw [coe_smul_root, wordProd_smul]
  change ([2, 0, 1, 3] : List (Fin 4)).foldr (reflect .D4)
    (Pi.single (2 : Fin 4) 1) = d4Certificate.root 22
  decide +kernel

theorem d4_commutator (s u : K) :
    xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) s *
        (rootOperatorFamily TwistTag.D4.tag).eltElement (rootAt TwistTag.D4.tag 19 (by decide)) u *
        (xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) s)⁻¹ *
        ((rootOperatorFamily TwistTag.D4.tag).eltElement
          (rootAt TwistTag.D4.tag 19 (by decide)) u)⁻¹ =
      (rootOperatorFamily TwistTag.D4.tag).eltElement (rootAt TwistTag.D4.tag 22 (by decide))
        (s * u) := by
  have h := commutator_eltElement_of_repCheck (τ := TwistTag.D4.tag) (K := K) d4_allValid
    (a := 2) (b := 19) (g := 22) (C := 1) (by decide +kernel) (by decide)
    (rootPos_simpleRoot (τ := TwistTag.D4.tag) ⟨2, by decide⟩)
    (rootPos_rootAt (τ := TwistTag.D4.tag) (by decide : 19 < _)) s u
  rw [eltElement_simpleRoot] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem d4_weylTwist_w :
    weylTwist TwistTag.D4
      ((coxeterSystem TwistTag.D4.tag).wordProd (twistOrbitWord .D4 ⟨0, by decide⟩)) =
      (coxeterSystem TwistTag.D4.tag).wordProd (twistOrbitWord .D4 ⟨0, by decide⟩) :=
  weylTwist_wordProd_eq (by decide +kernel)

theorem d4_weylTwist_w' :
    weylTwist TwistTag.D4 ((coxeterSystem TwistTag.D4.tag).wordProd
      (twistOrbitWord .D4 ⟨2, by decide⟩ ++ twistOrbitWord .D4 ⟨0, by decide⟩)) =
      (coxeterSystem TwistTag.D4.tag).wordProd
        (twistOrbitWord .D4 ⟨2, by decide⟩ ++ twistOrbitWord .D4 ⟨0, by decide⟩) :=
  weylTwist_wordProd_eq (by decide +kernel)

theorem d4_xElement_two_mem {c : K} (hc : σ c = c) :
    xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) c ∈ twistDerived .D4 K σ := by
  have hw := d4_weylTwist_w
  have hw' := d4_weylTwist_w'
  obtain ⟨ε, hε, h⟩ := exists_conj_nrep (K := K)
    ((coxeterSystem TwistTag.D4.tag).wordProd (twistOrbitWord .D4 ⟨0, by decide⟩))
    (simpleRoot TwistTag.D4.tag ⟨2, by decide⟩)
  rw [d4_w_smul] at h
  have hv : (rootOperatorFamily TwistTag.D4.tag).eltElement
      (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K) ∈ twistFixed .D4 K σ := by
    have h1 := h ε
    have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
    rw [hεε, eltElement_simpleRoot] at h1
    rw [← h1]
    exact mul_mem (mul_mem (nrep_mem_twistFixed' hw)
      (xElement_mem_twistFixed (by decide) (ringHom_eq_of_sign hε)))
      (inv_mem (nrep_mem_twistFixed' hw))
  have hθ : ∀ c : K, σ c = c → (rootOperatorFamily TwistTag.D4.tag).eltElement
      (rootAt TwistTag.D4.tag 22 (by decide)) c ∈ twistDerived .D4 K σ := by
    intro c hc
    have h2 := d4_commutator (K := K) c 1
    rw [mul_one] at h2
    rw [← h2]
    exact commutator_mem_twistDerived (xElement_mem_twistFixed (by decide) hc) hv
  rw [← eltElement_simpleRoot]
  exact mem_twistDerived_of_conj hw' d4_w'_smul hθ hc

end D4

variable [Finite K]

omit [Finite K] in
theorem torus2_conj_xElement (i j k : Fin t.tag.rank) (u v : Kˣ) (c : K) :
    torusElement t.tag K i u * torusElement t.tag K j v * xElement k c *
        (torusElement t.tag K i u * torusElement t.tag K j v)⁻¹ =
      xElement k (((u ^ t.tag.cartan i k : Kˣ) : K) * (((v ^ t.tag.cartan j k : Kˣ) : K) * c)) := by
  have e : ∀ a b x : adjointGroup t.tag K, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ :=
    fun a b x => by group
  rw [e, torusElement_conj_xElement, torusElement_conj_xElement]

omit [Finite K] in
theorem orbit2_mem_twistDerived {i j : Fin t.tag.rank} (hij : i ≠ j) (hρi : t.perm i = j)
    (hρj : t.perm j = i) (hcij : t.tag.cartan i j = 0) (hcji : t.tag.cartan j i = 0)
    (hσ2 : ∀ c, σ (σ c) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) (c : K) :
    xElement i c * xElement j (σ c) ∈ twistDerived t K σ := by
  set y : K → adjointGroup t.tag K := fun c => xElement i c * xElement j (σ c) with hy
  have hcomm : ∀ a b : K, xElement j b * xElement i a = xElement i a * xElement j b := fun a b =>
    (commute_of_mem_simple hij.symm hcji (xElement_mem_X j b) (xElement_mem_X i a)).eq
  have hfix : ∀ c, y c ∈ twistFixed t K σ := by
    intro c
    rw [mem_twistFixed, hy, map_mul, twistC_xElement, twistC_xElement, hρi, hρj, hσ2, hcomm]
  set v : Kˣ := Units.map σ.toMonoidHom u with hv
  have hvv : Units.map σ.toMonoidHom v = u := Units.ext (hσ2 u)
  have hh : torusElement t.tag K i u * torusElement t.tag K j v ∈ twistFixed t K σ := by
    rw [mem_twistFixed, map_mul, twistC_torusElement, twistC_torusElement, hρi, hρj, hvv]
    exact (torusElement_commute _ _ _ _).eq
  have hii : t.tag.cartan i i = 2 := Tag.cartan_self _ _
  have hjj : t.tag.cartan j j = 2 := Tag.cartan_self _ _
  have hconj : ∀ c, torusElement t.tag K i u * torusElement t.tag K j v * y c *
      (torusElement t.tag K i u * torusElement t.tag K j v)⁻¹ = y ((u : K) ^ 2 * c) := by
    intro c
    have e : ∀ (g a b : adjointGroup t.tag K), g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) :=
      fun g a b => by group
    rw [hy]
    simp only
    rw [e, torus2_conj_xElement, torus2_conj_xElement, hii, hjj, hcij, hcji]
    simp only [zpow_zero, Units.val_one, one_mul, zpow_two, Units.val_mul, hv]
    congr 2
    · ring
    · simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul,
        map_pow]
      ring
  have hsub : ∀ a b, y a * (y b)⁻¹ = y (a - b) := by
    intro a b
    rw [hy]
    simp only
    rw [mul_inv_rev, xElement_inv, xElement_inv, map_sub, sub_eq_add_neg (σ a),
      sub_eq_add_neg a, xElement_add i, xElement_add j]
    have h1 : xElement j (σ a) * (xElement j (-σ b) * xElement i (-b)) =
        xElement i (-b) * (xElement j (σ a) * xElement j (-σ b)) := by
      rw [← mul_assoc, ← xElement_add j, hcomm, xElement_add j]
    rw [mul_assoc, h1, ← mul_assoc]
  have hu1 : (u : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hu
  set c' := c / ((u : K) ^ 2 - 1)
  have hc : c = (u : K) ^ 2 * c' - c' := by
    rw [← sub_one_mul, mul_comm]
    exact (div_mul_cancel₀ c hu1).symm
  have : y c = torusElement t.tag K i u * torusElement t.tag K j v * y c' *
      (torusElement t.tag K i u * torusElement t.tag K j v)⁻¹ * (y c')⁻¹ := by
    rw [hconj, hsub, ← hc]
  change y c ∈ _
  rw [this]
  exact commutator_mem_twistDerived hh (hfix c')

omit [Finite K] in
theorem torus3_conj_xElement (i j k l : Fin t.tag.rank) (u v w : Kˣ) (c : K) :
    torusElement t.tag K i u * torusElement t.tag K j v * torusElement t.tag K k w * xElement l c *
        (torusElement t.tag K i u * torusElement t.tag K j v * torusElement t.tag K k w)⁻¹ =
      xElement l (((u ^ t.tag.cartan i l : Kˣ) : K) * (((v ^ t.tag.cartan j l : Kˣ) : K) *
        (((w ^ t.tag.cartan k l : Kˣ) : K) * c))) := by
  have e : ∀ a b x : adjointGroup t.tag K, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ :=
    fun a b x => by group
  rw [e, torusElement_conj_xElement, torus2_conj_xElement]

theorem mul3_mul_mul3 {G : Type*} [Group G] {a b c a' b' c' : G} (h1 : Commute b a')
    (h2 : Commute c a') (h3 : Commute c b') :
    a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') := by
  calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
    _ = a * (b * a') * c * b' * c' := by rw [h2.eq]; group
    _ = a * a' * b * (c * b') * c' := by rw [h1.eq]; group
    _ = a * a' * (b * b') * (c * c') := by rw [h3.eq]; group

omit [Finite K] in
theorem orbit3_mem_twistDerived {i j k : Fin t.tag.rank} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hρi : t.perm i = j) (hρj : t.perm j = k) (hρk : t.perm k = i)
    (hcij : t.tag.cartan i j = 0) (hcji : t.tag.cartan j i = 0) (hcik : t.tag.cartan i k = 0)
    (hcki : t.tag.cartan k i = 0) (hcjk : t.tag.cartan j k = 0) (hckj : t.tag.cartan k j = 0)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) (c : K) :
    xElement i c * xElement j (σ c) * xElement k (σ (σ c)) ∈ twistDerived t K σ := by
  set y : K → adjointGroup t.tag K :=
    fun c => xElement i c * xElement j (σ c) * xElement k (σ (σ c)) with hy
  have cm : ∀ {p q : Fin t.tag.rank}, p ≠ q → t.tag.cartan p q = 0 → ∀ a b : K,
      Commute (xElement p a) (xElement q b) := fun hpq hc a b =>
    commute_of_mem_simple hpq hc (xElement_mem_X _ a) (xElement_mem_X _ b)
  have hfix : ∀ c, y c ∈ twistFixed t K σ := by
    intro c
    rw [mem_twistFixed, hy]
    simp only [map_mul, twistC_xElement, hρi, hρj, hρk, hσ3]
    rw [mul_assoc, (cm hik.symm hcki _ _).eq, ← mul_assoc, (cm hij.symm hcji _ _).eq]
  set v : Kˣ := Units.map σ.toMonoidHom u with hv
  set w : Kˣ := Units.map σ.toMonoidHom v with hw
  have hwu : Units.map σ.toMonoidHom w = u := Units.ext (hσ3 u)
  set h := torusElement t.tag K i u * torusElement t.tag K j v * torusElement t.tag K k w
  have hh : h ∈ twistFixed t K σ := by
    rw [mem_twistFixed, map_mul, map_mul, twistC_torusElement, twistC_torusElement,
      twistC_torusElement, hρi, hρj, hρk, ← hv, ← hw, hwu]
    rw [mul_assoc, (torusElement_commute k i w u).eq, ← mul_assoc,
      (torusElement_commute j i v u).eq]
  have hii : t.tag.cartan i i = 2 := Tag.cartan_self _ _
  have hjj : t.tag.cartan j j = 2 := Tag.cartan_self _ _
  have hkk : t.tag.cartan k k = 2 := Tag.cartan_self _ _
  have hσu : ∀ x : Kˣ, ((Units.map σ.toMonoidHom x : Kˣ) : K) = σ x := fun _ => rfl
  have hconj : ∀ c, h * y c * h⁻¹ = y ((u : K) ^ 2 * c) := by
    intro c
    have e : ∀ (g a b d : adjointGroup t.tag K),
        g * (a * b * d) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * d * g⁻¹) :=
      fun g a b d => by group
    rw [hy]
    simp only
    rw [e, torus3_conj_xElement, torus3_conj_xElement, torus3_conj_xElement, hii, hjj, hkk, hcij,
      hcji, hcik, hcki, hcjk, hckj]
    simp only [zpow_zero, Units.val_one, one_mul, zpow_two, Units.val_mul, hσu, hv, hw]
    simp only [map_mul, map_pow]
    congr 3 <;> ring
  have hadd : ∀ a b, y a * y b = y (a + b) := by
    intro a b
    rw [hy]
    simp only
    rw [mul3_mul_mul3 ((cm hij.symm hcji _ _)) ((cm hik.symm hcki _ _)) ((cm hjk.symm hckj _ _)),
      ← xElement_add, ← xElement_add, ← xElement_add]
    simp only [map_add]
  have hinv : ∀ b, (y b)⁻¹ = y (-b) := fun b => by
    rw [inv_eq_iff_mul_eq_one, hadd, add_neg_cancel, hy]
    simp only [map_zero, xElement_zero, mul_one]
  have hu1 : (u : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hu
  set c' := c / ((u : K) ^ 2 - 1)
  have hc : c = (u : K) ^ 2 * c' + -c' := by
    rw [← sub_eq_add_neg, ← sub_one_mul, mul_comm]
    exact (div_mul_cancel₀ c hu1).symm
  have : y c = h * y c' * h⁻¹ * (y c')⁻¹ := by
    rw [hconj, hinv, hadd, ← hc]
  change y c ∈ _
  rw [this]
  exact commutator_mem_twistDerived hh (hfix c')

omit [Finite K] in
theorem fixed_mem_of_singleton {i : Fin t.tag.rank} (hi : t.perm i = i)
    {ω : List (Fin t.tag.rank)} (hsupp : supportCheck t.tag ω [i] = true)
    (hmem : ∀ c : K, σ c = c → xElement i c ∈ twistDerived t K σ) {y : adjointGroup t.tag K}
    (hy : y ∈ Uminus t.tag K ((coxeterSystem t.tag).wordProd ω)) (hF : twistC t K σ y = y) :
    y ∈ twistDerived t K σ := by
  have hle := Uminus_le_of_supportCheck K hsupp hy
  have hX : y ∈ (nativeRootSubgroups t.tag K).X (simpleRoot t.tag i) := by
    refine (iSup₂_le fun l hl => ?_ : (⨆ (l : Fin t.tag.rank) (_ : l ∈ [i]),
      (nativeRootSubgroups t.tag K).X (simpleRoot t.tag l)) ≤ _) hle
    rw [List.mem_singleton.1 hl]
  obtain ⟨a, rfl⟩ := exists_eq_xElement_of_mem hX
  rw [twistC_xElement, hi] at hF
  exact hmem a (xElement_injective i hF)

theorem fixed_mem_of_orbit2 {i j : Fin t.tag.rank} (hij : i ≠ j) (hρi : t.perm i = j)
    (hρj : t.perm j = i) (hcij : t.tag.cartan i j = 0) (hcji : t.tag.cartan j i = 0)
    {ω : List (Fin t.tag.rank)} (hsupp : supportCheck t.tag ω [i, j] = true)
    (hσ2 : ∀ c, σ (σ c) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) {y : adjointGroup t.tag K}
    (hy : y ∈ Uminus t.tag K ((coxeterSystem t.tag).wordProd ω)) (hF : twistC t K σ y = y) :
    y ∈ twistDerived t K σ := by
  have hle := Uminus_le_of_supportCheck K hsupp hy
  have hX : y ∈ (nativeRootSubgroups t.tag K).X (simpleRoot t.tag i) ⊔
      (nativeRootSubgroups t.tag K).X (simpleRoot t.tag j) := by
    refine (iSup₂_le fun l hl => ?_ : (⨆ (l : Fin t.tag.rank) (_ : l ∈ [i, j]),
      (nativeRootSubgroups t.tag K).X (simpleRoot t.tag l)) ≤ _) hle
    rcases List.mem_pair.1 hl with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  obtain ⟨a, b, rfl⟩ := exists_eq_xElement_mul_of_mem_sup hij hcij hX
  rw [map_mul, twistC_xElement, twistC_xElement, hρi, hρj,
    ← (commute_of_mem_simple hij hcij (xElement_mem_X i (σ b)) (xElement_mem_X j (σ a))).eq]
    at hF
  obtain ⟨hba, hab⟩ := eq_of_xElement_mul_xElement_eq hij hF
  rw [← hab]
  exact orbit2_mem_twistDerived hij hρi hρj hcij hcji hσ2 hu a

theorem fixed_mem_of_orbit3 {i j k : Fin t.tag.rank} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hρi : t.perm i = j) (hρj : t.perm j = k) (hρk : t.perm k = i)
    (hcij : t.tag.cartan i j = 0) (hcji : t.tag.cartan j i = 0) (hcik : t.tag.cartan i k = 0)
    (hcki : t.tag.cartan k i = 0) (hcjk : t.tag.cartan j k = 0) (hckj : t.tag.cartan k j = 0)
    {ω : List (Fin t.tag.rank)} (hsupp : supportCheck t.tag ω [i, j, k] = true)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) {y : adjointGroup t.tag K}
    (hy : y ∈ Uminus t.tag K ((coxeterSystem t.tag).wordProd ω)) (hF : twistC t K σ y = y) :
    y ∈ twistDerived t K σ := by
  have hle := Uminus_le_of_supportCheck K hsupp hy
  have hX : y ∈ (nativeRootSubgroups t.tag K).X (simpleRoot t.tag i) ⊔
      (nativeRootSubgroups t.tag K).X (simpleRoot t.tag j) ⊔
        (nativeRootSubgroups t.tag K).X (simpleRoot t.tag k) := by
    refine (iSup₂_le fun l hl => ?_ : (⨆ (l : Fin t.tag.rank) (_ : l ∈ [i, j, k]),
      (nativeRootSubgroups t.tag K).X (simpleRoot t.tag l)) ≤ _) hle
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  obtain ⟨a, b, c, rfl⟩ :=
    exists_eq_xElement_mul_mul_of_mem_sup hij hik hjk hcij hcik hcjk hX
  have cm : ∀ {p q : Fin t.tag.rank}, p ≠ q → t.tag.cartan p q = 0 → ∀ a b : K,
      Commute (xElement p a) (xElement q b) := fun hpq hc a b =>
    commute_of_mem_simple hpq hc (xElement_mem_X _ a) (xElement_mem_X _ b)
  simp only [map_mul, twistC_xElement, hρi, hρj, hρk] at hF
  rw [mul_assoc, (cm hik.symm hcki _ _).eq, ← mul_assoc, (cm hij.symm hcji _ _).eq] at hF
  obtain ⟨hca, hab, hbc⟩ := eq_of_xElement_mul_mul_eq hij hik hjk hF
  rw [← hab, ← hbc, ← hab]
  exact orbit3_mem_twistDerived hij hik hjk hρi hρj hρk hcij hcji hcik hcki hcjk hckj hσ3 hu a

variable (t) in
@[expose] def twistBlocks : (t : TwistTag) → List (List (Fin t.tag.rank))
  | .E6 => (List.replicate 6 [twistOrbitWord .E6 ⟨1, by decide⟩, twistOrbitWord .E6 ⟨2, by decide⟩,
      twistOrbitWord .E6 ⟨3, by decide⟩, twistOrbitWord .E6 ⟨0, by decide⟩]).flatten
  | .D4 => (List.replicate 3
      [twistOrbitWord .D4 ⟨2, by decide⟩, twistOrbitWord .D4 ⟨0, by decide⟩]).flatten

theorem weylTwist_twistBlocks {ω : List (Fin t.tag.rank)} (hω : ω ∈ twistBlocks t) :
    weylTwist t ((coxeterSystem t.tag).wordProd ω) = (coxeterSystem t.tag).wordProd ω := by
  have : ∃ i, ω = twistOrbitWord t i := by
    cases t
    · simp only [twistBlocks, List.mem_flatten, List.mem_replicate] at hω
      obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hω
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with h | h | h | h <;> exact ⟨_, h⟩
    · simp only [twistBlocks, List.mem_flatten, List.mem_replicate] at hω
      obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hω
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with h | h <;> exact ⟨_, h⟩
  obtain ⟨i, rfl⟩ := this
  exact twistOrbitWord_mem t i

theorem e6_U_le_twistDerived (hσ : Function.Surjective σ) (hσ2 : ∀ c, σ (σ c) = c) {u : Kˣ}
    (hu : (u : K) ^ 2 ≠ 1) :
    ∀ x ∈ (nativeData TwistTag.E6.tag K).U, twistC .E6 K σ x = x →
      x ∈ twistDerived .E6 K σ := by
  refine fixed_mem_U_of_reduced_blocks (twistEquiv .E6 K σ hσ) (weylTwist .E6)
    (fun _ hx => twistC_mem_U .E6 K σ hx) (twistEquiv_mem_Uminus .E6 K σ hσ)
    (twistEquiv_nrep .E6 K σ hσ) (twistBlocks .E6) (fun ω hω => weylTwist_twistBlocks hω)
    (isReduced_of_reducedCheck (by decide +kernel))
    (height_wordProd_smul_neg_of_negCheck (by decide +kernel)) _
    (fun g hg x hx => conj_mem_twistDerived hg hx) ?_
  intro ω hω y hy hF
  change twistC .E6 K σ y = y at hF
  simp only [twistBlocks, List.mem_flatten, List.mem_replicate] at hω
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hω
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact fixed_mem_of_singleton (i := ⟨1, by decide⟩) (by decide) (by decide +kernel)
      (fun c hc => e6_xElement_one_mem hc) hy hF
  · exact fixed_mem_of_orbit2 (i := ⟨2, by decide⟩) (j := ⟨4, by decide⟩) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel) hσ2 hu hy hF
  · exact fixed_mem_of_singleton (i := ⟨3, by decide⟩) (by decide) (by decide +kernel)
      (fun c hc => e6_xElement_three_mem hc) hy hF
  · exact fixed_mem_of_orbit2 (i := ⟨0, by decide⟩) (j := ⟨5, by decide⟩) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel) hσ2 hu hy hF

theorem d4_U_le_twistDerived (hσ : Function.Surjective σ) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) :
    ∀ x ∈ (nativeData TwistTag.D4.tag K).U, twistC .D4 K σ x = x →
      x ∈ twistDerived .D4 K σ := by
  refine fixed_mem_U_of_reduced_blocks (twistEquiv .D4 K σ hσ) (weylTwist .D4)
    (fun _ hx => twistC_mem_U .D4 K σ hx) (twistEquiv_mem_Uminus .D4 K σ hσ)
    (twistEquiv_nrep .D4 K σ hσ) (twistBlocks .D4) (fun ω hω => weylTwist_twistBlocks hω)
    (isReduced_of_reducedCheck (by decide +kernel))
    (height_wordProd_smul_neg_of_negCheck (by decide +kernel)) _
    (fun g hg x hx => conj_mem_twistDerived hg hx) ?_
  intro ω hω y hy hF
  change twistC .D4 K σ y = y at hF
  simp only [twistBlocks, List.mem_flatten, List.mem_replicate] at hω
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hω
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact fixed_mem_of_singleton (i := ⟨2, by decide⟩) (by decide) (by decide +kernel)
      (fun c hc => d4_xElement_two_mem hc) hy hF
  · exact fixed_mem_of_orbit3 (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) (k := ⟨3, by decide⟩)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) hσ3 hu hy hF

end CFSG.LieType.Chevalley

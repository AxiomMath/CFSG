module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.QuasithinUnique.Setup.Offender

universe u

theorem isSubnormal_of_isNilpotent {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (H : Subgroup G) : H.IsSubnormal := by
  suffices h : ∀ n : ℕ, ∀ K : Subgroup G, K.index = n → K.IsSubnormal from h _ H rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hn
    by_cases hK : K = ⊤
    · rw [hK]; exact Subgroup.IsSubnormal.top
    · have hlt : K < ⊤ := lt_top_iff_ne_top.2 hK
      have hN : K < Subgroup.normalizer (K : Set G) :=
        Group.normalizerCondition_of_isNilpotent K hlt
      have hidx : (Subgroup.normalizer (K : Set G)).index < K.index :=
        Subgroup.index_strictAnti hN
      exact Subgroup.IsSubnormal.step K _ hN.le (ih _ (hn ▸ hidx) _ rfl) inferInstance

theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] (hodd : Odd (Nat.card G)) {x : G}
    (hx : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h2
    obtain ⟨m, hm⟩ := hodd
    omega

section Eigen

variable {F : Type*} [Group F]

@[expose] def eigenSub (N : Subgroup F) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (b : MulAut F)
    (ε : ℤˣ) : Subgroup F where
  carrier := {y | y ∈ N ∧ b y = y ^ (ε : ℤ)}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨N.mul_mem hx.1 hy.1, by
    have hxy : Commute x y := hN x hx.1 y hy.1
    rw [map_mul, hx.2, hy.2, hxy.mul_zpow]⟩
  inv_mem' := fun {x} hx => ⟨N.inv_mem hx.1, by rw [map_inv, hx.2, inv_zpow]⟩

theorem exists_common_eigenelement (𝒯 : Set (MulAut F)) (h2 : ∀ b ∈ 𝒯, b * b = 1)
    (hc : ∀ b ∈ 𝒯, ∀ c ∈ 𝒯, b * c = c * b) (S : Finset (MulAut F))
    (hS : (S : Set (MulAut F)) ⊆ 𝒯) :
    ∀ N : Subgroup F, N ≠ ⊥ → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) →
      (∀ x ∈ N, x ^ 2 = 1 → x = 1) → (∀ b ∈ 𝒯, ∀ x ∈ N, b x ∈ N) →
      ∃ x ∈ N, x ≠ 1 ∧ ∀ b ∈ S, ∃ ε : ℤˣ, b x = x ^ (ε : ℤ) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro _ N hN _ _ _
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h), by simp⟩
  | insert b S hbS ih =>
    intro hS N hN hcomm hno hinv
    have hb : b ∈ 𝒯 := hS (Finset.mem_insert_self b S)
    have hSsub : (S : Set (MulAut F)) ⊆ 𝒯 := fun c hc' => hS (Finset.mem_insert_of_mem hc')
    obtain ⟨⟨x, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hbb : ∀ y, b (b y) = y := fun y => by
      have := congrArg (fun e : MulAut F => e y) (h2 b hb)
      simpa using this
    have hbxN : b x ∈ N := hinv b hb x hxN
    have hxcomm : x * b x = b x * x := hcomm x hxN (b x) hbxN
    have key : ∀ (ε : ℤˣ) (z : F), z ∈ eigenSub N hcomm b ε → z ≠ 1 →
        ∃ y ∈ N, y ≠ 1 ∧ ∀ c ∈ insert b S, ∃ ε' : ℤˣ, c y = y ^ (ε' : ℤ) := by
      intro ε z hz hz1
      have hN' : eigenSub N hcomm b ε ≠ ⊥ := fun h =>
        hz1 (Subgroup.mem_bot.1 (h ▸ hz))
      have hinv' : ∀ c ∈ 𝒯, ∀ u ∈ eigenSub N hcomm b ε, c u ∈ eigenSub N hcomm b ε := by
        intro c hc' u hu
        refine ⟨hinv c hc' u hu.1, ?_⟩
        have hbc : b (c u) = c (b u) := congrArg (fun e : MulAut F => e u) (hc b hb c hc')
        rw [hbc, hu.2, map_zpow]
      obtain ⟨y, hyN, hy1, hyS⟩ := ih hSsub (eigenSub N hcomm b ε) hN'
        (fun u hu v hv => hcomm u hu.1 v hv.1) (fun u hu h => hno u hu.1 h) hinv'
      refine ⟨y, hyN.1, hy1, fun c hc' => ?_⟩
      rcases Finset.mem_insert.1 hc' with rfl | hcS
      · exact ⟨ε, hyN.2⟩
      · exact hyS c hcS
    have hmem_p : x * b x ∈ eigenSub N hcomm b 1 := by
      refine ⟨N.mul_mem hxN hbxN, ?_⟩
      simp [hbb, hxcomm]
    have hmem_m : x * (b x)⁻¹ ∈ eigenSub N hcomm b (-1) := by
      refine ⟨N.mul_mem hxN (N.inv_mem hbxN), ?_⟩
      simp [hbb]
    by_cases hp : x * b x = 1
    · refine key (-1) _ hmem_m ?_
      intro hm
      have h1 : x = b x := mul_inv_eq_one.1 hm
      have hsq : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := pow_two x
          _ = x * b x := by rw [← h1]
          _ = 1 := hp
      exact hx1' (hno x hxN hsq)
    · exact key 1 _ hmem_p hp

theorem exists_eigenelement_of_commutative [Finite F] (𝒯 : Set (MulAut F))
    (h2 : ∀ b ∈ 𝒯, b * b = 1) (hc : ∀ b ∈ 𝒯, ∀ c ∈ 𝒯, b * c = c * b)
    (M : Subgroup F) (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hno : ∀ x ∈ M, x ^ 2 = 1 → x = 1)
    (hinv : ∀ b ∈ 𝒯, ∀ x ∈ M, b x ∈ M) {a : MulAut F} (ha : a ∈ 𝒯) {y : F} (hy : y ∈ M)
    (hay : a y ≠ y) :
    ∃ x ∈ M, x ≠ 1 ∧ a x = x⁻¹ ∧ ∀ b ∈ 𝒯, ∃ ε : ℤˣ, b x = x ^ (ε : ℤ) := by
  classical
  have : Finite (MulAut F) :=
    Finite.of_injective (fun e : MulAut F => (e : F → F)) DFunLike.coe_injective
  have haa : ∀ z, a (a z) = z := fun z => by
    have := congrArg (fun e : MulAut F => e z) (h2 a ha)
    simpa using this
  have hayM : a y ∈ M := hinv a ha y hy
  have hz : y * (a y)⁻¹ ∈ eigenSub M hM a (-1) := by
    refine ⟨M.mul_mem hy (M.inv_mem hayM), ?_⟩
    simp [haa]
  have hz1 : y * (a y)⁻¹ ≠ 1 := fun h => hay (mul_inv_eq_one.1 h).symm
  have hN : eigenSub M hM a (-1) ≠ ⊥ := fun h => hz1 (Subgroup.mem_bot.1 (h ▸ hz))
  have hNinv : ∀ b ∈ 𝒯, ∀ x ∈ eigenSub M hM a (-1), b x ∈ eigenSub M hM a (-1) := by
    intro b hb x hx
    refine ⟨hinv b hb x hx.1, ?_⟩
    have hab : a (b x) = b (a x) := congrArg (fun e : MulAut F => e x) (hc a ha b hb)
    rw [hab, hx.2, map_zpow]
  obtain ⟨x, hxN, hx1, hx⟩ := exists_common_eigenelement 𝒯 h2 hc (Set.toFinite 𝒯).toFinset
    (by intro b hb; simpa using hb) (eigenSub M hM a (-1)) hN
    (fun u hu v hv => hM u hu.1 v hv.1) (fun u hu h => hno u hu.1 h) hNinv
  refine ⟨x, hxN.1, hx1, ?_, fun b hb => hx b (by simpa using hb)⟩
  have := hxN.2
  simpa using this

end Eigen

section Centre

variable {F : Type*} [Group F]

@[expose] def centerQuotAut (b : MulAut F) : MulAut (F ⧸ Subgroup.center F) :=
  QuotientGroup.congr _ _ b (Subgroup.characteristic_iff_map_eq.1 inferInstance b)

theorem centerQuotAut_mk (b : MulAut F) (x : F) :
    centerQuotAut b (x : F ⧸ Subgroup.center F) = ((b x : F) : F ⧸ Subgroup.center F) := rfl

theorem mem_center_of_aut (b : MulAut F) {z : F} (hz : z ∈ Subgroup.center F) :
    b z ∈ Subgroup.center F := by
  have h : b.toMonoidHom z ∈ (Subgroup.center F).map b.toMonoidHom :=
    Subgroup.mem_map_of_mem _ hz
  rw [Subgroup.characteristic_iff_map_eq.1 inferInstance b] at h
  exact h

end Centre

theorem exists_eigenelement_nilpotent :
    ∀ (n : ℕ) (F : Type u) [Group F] [Finite F] [Group.IsNilpotent F], Nat.card F = n → Odd n →
      ∀ 𝒯 : Set (MulAut F), (∀ b ∈ 𝒯, b * b = 1) → (∀ b ∈ 𝒯, ∀ c ∈ 𝒯, b * c = c * b) →
      (∃ b ∈ 𝒯, b ≠ 1) →
      ∃ x : F, x ≠ 1 ∧ (∀ b ∈ 𝒯, ∃ ε : ℤˣ, b x = x ^ (ε : ℤ)) ∧ ∃ b ∈ 𝒯, b x = x⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F _ _ _ hn hodd 𝒯 h2 hc hnt
  have hodd' : Odd (Nat.card F) := hn ▸ hodd
  have hno : ∀ x : F, x ^ 2 = 1 → x = 1 := fun x hx => eq_one_of_sq_eq_one_of_odd hodd' hx
  obtain ⟨a, ha, ha1⟩ := hnt
  have hmove : ∃ y : F, a y ≠ y := by
    by_contra h
    exact ha1 (MulEquiv.ext fun y => by by_contra hne; exact h ⟨y, hne⟩)
  obtain ⟨y0, hy0⟩ := hmove
  have : Nontrivial F := ⟨⟨y0, 1, fun h => hy0 (by rw [h, map_one])⟩⟩
  have hZne : Subgroup.center F ≠ ⊥ := Group.IsNilpotent.center_ne_bot F
  by_cases hact : ∃ b ∈ 𝒯, ∃ z ∈ Subgroup.center F, b z ≠ z
  ·
    obtain ⟨b, hb, z, hz, hbz⟩ := hact
    obtain ⟨x, -, hx1, hbx, hx⟩ := exists_eigenelement_of_commutative 𝒯 h2 hc (Subgroup.center F)
      (fun u hu v _ => (Subgroup.mem_center_iff.1 hu v).symm) (fun x _ hx => hno x hx)
      (fun b _ x hx => mem_center_of_aut b hx) hb hz hbz
    exact ⟨x, hx1, hx, b, hb, hbx⟩
  · have hfix : ∀ b ∈ 𝒯, ∀ z ∈ Subgroup.center F, b z = z := by
      intro b hb z hz
      by_contra hne
      exact hact ⟨b, hb, z, hz, hne⟩
    have hZodd : Nat.Coprime 2 (Nat.card (Subgroup.center F)) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h2z => ?_
      have hd : Nat.card (Subgroup.center F) ∣ Nat.card F := Subgroup.card_subgroup_dvd_card _
      obtain ⟨m, hm⟩ := hodd'
      have := dvd_trans h2z hd
      omega
    obtain ⟨𝒯', h𝒯'⟩ : ∃ T : Set (MulAut (F ⧸ Subgroup.center F)), T = centerQuotAut '' 𝒯 :=
      ⟨_, rfl⟩
    have hmem : ∀ c, c ∈ 𝒯' ↔ ∃ b ∈ 𝒯, centerQuotAut b = c := fun c => by
      rw [h𝒯']; exact Set.mem_image _ _ _
    have h2q : ∀ c ∈ 𝒯', c * c = 1 := by
      intro c hc'
      obtain ⟨b, hb, rfl⟩ := (hmem c).1 hc'
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | _ x =>
        show centerQuotAut b (centerQuotAut b (x : F ⧸ Subgroup.center F)) = x
        rw [centerQuotAut_mk, centerQuotAut_mk]
        have := congrArg (fun e : MulAut F => e x) (h2 b hb)
        exact congrArg (fun z : F => (z : F ⧸ Subgroup.center F)) this
    have hcq : ∀ c ∈ 𝒯', ∀ d ∈ 𝒯', c * d = d * c := by
      intro c hc' d hd'
      obtain ⟨b, hb, rfl⟩ := (hmem c).1 hc'
      obtain ⟨b', hb', rfl⟩ := (hmem d).1 hd'
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | _ x =>
        show centerQuotAut b (centerQuotAut b' (x : F ⧸ Subgroup.center F)) =
          centerQuotAut b' (centerQuotAut b (x : F ⧸ Subgroup.center F))
        rw [centerQuotAut_mk, centerQuotAut_mk, centerQuotAut_mk, centerQuotAut_mk]
        have := congrArg (fun e : MulAut F => e x) (hc b hb b' hb')
        exact congrArg (fun z : F => (z : F ⧸ Subgroup.center F)) this
    have hntq : ∃ c ∈ 𝒯', c ≠ 1 := by
      by_contra hcon
      have hbar1 : centerQuotAut a = 1 := by
        by_contra hne
        exact hcon ⟨_, (hmem _).2 ⟨a, ha, rfl⟩, hne⟩
      refine ha1 (CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
        (Subgroup.center F) a 2 (by rw [pow_two]; exact h2 a ha) hZodd (hfix a ha) ?_)
      intro x
      have h1 : centerQuotAut a (x : F ⧸ Subgroup.center F) = (x : F ⧸ Subgroup.center F) := by
        rw [hbar1]; rfl
      rw [centerQuotAut_mk] at h1
      exact QuotientGroup.eq.1 h1.symm
    have hcardQ : Nat.card (F ⧸ Subgroup.center F) * Nat.card (Subgroup.center F) = Nat.card F :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center F)).symm
    have hZgt : 1 < Nat.card (Subgroup.center F) :=
      (Subgroup.center F).one_lt_card_iff_ne_bot.2 hZne
    have hQpos : 0 < Nat.card (F ⧸ Subgroup.center F) := Nat.card_pos
    have hQlt : Nat.card (F ⧸ Subgroup.center F) < n := by
      rw [← hn, ← hcardQ]; nlinarith
    have hQodd : Odd (Nat.card (F ⧸ Subgroup.center F)) :=
      Odd.of_dvd_nat hodd' (Dvd.intro _ hcardQ)
    have hnoQ : ∀ q : F ⧸ Subgroup.center F, q ^ 2 = 1 → q = 1 := fun q hq =>
      eq_one_of_sq_eq_one_of_odd hQodd hq
    obtain ⟨xq, hxq1, hxq, c0, hc0, hc0x⟩ :=
      ih _ hQlt (F ⧸ Subgroup.center F) rfl hQodd 𝒯' h2q hcq hntq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective xq
    obtain ⟨b0, hb0, rfl⟩ := (hmem c0).1 hc0
    let M : Subgroup F := (Subgroup.zpowers (g : F ⧸ Subgroup.center F)).comap
      (QuotientGroup.mk' (Subgroup.center F))
    have hMdecomp : ∀ u ∈ M, ∃ (n : ℤ) (z : F), z ∈ Subgroup.center F ∧ u = g ^ n * z := by
      intro u hu
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hu
      refine ⟨n, (g ^ n)⁻¹ * u, ?_, by simp⟩
      rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
      exact hn
    have hMcomm : ∀ u ∈ M, ∀ v ∈ M, u * v = v * u := by
      intro u hu v hv
      obtain ⟨n, z, hz, rfl⟩ := hMdecomp u hu
      obtain ⟨m, z', hz', rfl⟩ := hMdecomp v hv
      have hcen : ∀ (w : F), ∀ t ∈ Subgroup.center F, Commute w t := fun w t ht =>
        Subgroup.mem_center_iff.1 ht w
      have hA : Commute (g ^ n) (g ^ m * z') :=
        Commute.mul_right ((Commute.refl g).zpow_zpow n m) (hcen _ z' hz')
      have hB : Commute z (g ^ m * z') :=
        Commute.mul_right (hcen (g ^ m) z hz).symm (hcen z z' hz')
      exact (Commute.mul_left hA hB).eq
    have hMinv : ∀ b ∈ 𝒯, ∀ u ∈ M, b u ∈ M := by
      intro b hb u hu
      obtain ⟨ε, hε⟩ := hxq (centerQuotAut b) ((hmem _).2 ⟨b, hb, rfl⟩)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hu
      show QuotientGroup.mk' (Subgroup.center F) (b u) ∈
        Subgroup.zpowers (g : F ⧸ Subgroup.center F)
      have hbu : QuotientGroup.mk' (Subgroup.center F) (b u) =
          centerQuotAut b (QuotientGroup.mk' (Subgroup.center F) u) := rfl
      rw [hbu, ← hn, map_zpow, hε, ← zpow_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    have hgM : g ∈ M := by
      show QuotientGroup.mk' (Subgroup.center F) g ∈ Subgroup.zpowers (g : F ⧸ Subgroup.center F)
      exact Subgroup.mem_zpowers _
    have hb0g : b0 g ≠ g := by
      intro h
      have h1 : centerQuotAut b0 (g : F ⧸ Subgroup.center F) = (g : F ⧸ Subgroup.center F) := by
        rw [centerQuotAut_mk, h]
      rw [h1] at hc0x
      apply hxq1
      apply hnoQ
      calc (g : F ⧸ Subgroup.center F) ^ 2 = (g : F ⧸ Subgroup.center F) * g := pow_two _
        _ = (g : F ⧸ Subgroup.center F) * (g : F ⧸ Subgroup.center F)⁻¹ :=
          congrArg (fun t => (g : F ⧸ Subgroup.center F) * t) hc0x
        _ = 1 := mul_inv_cancel _
    obtain ⟨x, -, hx1, hbx, hx⟩ := exists_eigenelement_of_commutative 𝒯 h2 hc M hMcomm
      (fun u _ hu => hno u hu) hMinv hb0 hgM hb0g
    exact ⟨x, hx1, hx, b0, hb0, hbx⟩

theorem elementary_two_action_on_odd_nilpotent_detects_invariant_cyclic_subgroup
    {F : Type u} [Group F] [Finite F] [Group.IsNilpotent F] (hodd : Odd (Nat.card F))
    {A : Type*} [Group A] [Finite A] [CFSG.IsElementaryAbelian 2 A]
    (φ : A →* MulAut F) (hφ : φ ≠ 1) :
    (∃ C : Subgroup F, C ≠ ⊥ ∧ IsCyclic C ∧ (∀ a : A, ∀ c ∈ C, φ a c ∈ C) ∧
      (∃ χ : A →* ℤˣ, χ ≠ 1 ∧ ∀ a : A, ∀ c ∈ C, φ a c = c ^ (χ a : ℤ)) ∧
      Subgroup.closure {x : F | ∃ a : A, ∃ c ∈ C, x = φ a c * c⁻¹} ≠ ⊥) ∧
    ∀ U : Subgroup F, U.IsSubnormal := by
  refine ⟨?_, fun U => isSubnormal_of_isNilpotent U⟩
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := A)).comm a b
  have hsq : ∀ a : A, a * a = 1 := fun a => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
    rwa [pow_two] at this
  have h2 : ∀ b ∈ Set.range φ, b * b = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, hsq a, map_one]
  have hc : ∀ b ∈ Set.range φ, ∀ c ∈ Set.range φ, b * c = c * b := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [← map_mul, ← map_mul, hcomm]
  have hnt : ∃ b ∈ Set.range φ, b ≠ 1 := by
    by_contra h
    exact hφ (MonoidHom.ext fun a => by
      by_contra hne
      exact h ⟨φ a, ⟨a, rfl⟩, hne⟩)
  obtain ⟨x, hx1, hx, b0, ⟨a0, rfl⟩, ha0x⟩ :=
    exists_eigenelement_nilpotent (Nat.card F) F rfl hodd (Set.range φ) h2 hc hnt
  have hxx : x ≠ x⁻¹ := by
    intro h
    apply hx1
    apply eq_one_of_sq_eq_one_of_odd hodd
    calc x ^ 2 = x * x := pow_two x
      _ = x * x⁻¹ := congrArg (fun t => x * t) h
      _ = 1 := mul_inv_cancel x
  have hexp : ∀ a : A, ∃ ε : ℤˣ, φ a x = x ^ (ε : ℤ) := fun a => hx (φ a) ⟨a, rfl⟩
  have huniq : ∀ ε ε' : ℤˣ, x ^ (ε : ℤ) = x ^ (ε' : ℤ) → ε = ε' := by
    intro ε ε' h
    rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl
    · rfl
    · exfalso; apply hxx; simpa using h
    · exfalso; apply hxx; simpa using h.symm
    · rfl
  choose χ' hχ' using hexp
  let χ : A →* ℤˣ :=
    { toFun := χ'
      map_one' := by
        apply huniq
        rw [← hχ' 1, map_one]; simp
      map_mul' := fun a b => by
        show χ' (a * b) = χ' a * χ' b
        apply huniq
        rw [← hχ' (a * b), map_mul]
        show φ a (φ b x) = _
        rw [hχ' b, map_zpow, hχ' a, ← zpow_mul, Units.val_mul] }
  have hχ : ∀ a : A, φ a x = x ^ ((χ a : ℤˣ) : ℤ) := hχ'
  have hχa0 : χ a0 = -1 := by
    apply huniq
    rw [← hχ a0, ha0x]
    simp
  refine ⟨Subgroup.zpowers x, ?_, inferInstance, ?_, ⟨χ, ?_, ?_⟩, ?_⟩
  · exact fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
  · intro a c hc'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    rw [map_zpow, hχ a]
    exact Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _) _
  · intro h
    have := congrArg (fun f : A →* ℤˣ => f a0) h
    simp [hχa0] at this
  · intro a c hc'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    rw [map_zpow, hχ a, ← zpow_mul, ← zpow_mul, mul_comm]
  · intro h
    have hmem : φ a0 x * x⁻¹ ∈ Subgroup.closure
        {y : F | ∃ a : A, ∃ c ∈ Subgroup.zpowers x, y = φ a c * c⁻¹} :=
      Subgroup.subset_closure ⟨a0, x, Subgroup.mem_zpowers x, rfl⟩
    rw [h, Subgroup.mem_bot, ha0x] at hmem
    have h1 := eq_one_of_sq_eq_one_of_odd hodd (x := x⁻¹) (by rw [pow_two]; exact hmem)
    exact hx1 (inv_eq_one.1 h1)

end CFSG.QuasithinUnique.Setup.Offender

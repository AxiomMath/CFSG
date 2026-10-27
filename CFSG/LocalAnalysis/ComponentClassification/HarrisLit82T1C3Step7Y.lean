module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step7

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L S : Subgroup G} {p f : ℕ}

omit [Finite G] in
theorem mem_pPrimeCore_of_normal {M N : Subgroup G} (hN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) {x : G} (hxM : x ∈ M) (hxN : x ∈ N) :
    (⟨x, hxM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
  have hNn : (N.subgroupOf M).Normal := ⟨fun n hn g => hN g g.2 n hn⟩
  have hdvd : Nat.card ↥(N.subgroupOf M) ∣ Nat.card ↥N := by
    rw [← Subgroup.card_map_of_injective M.subtype_injective, subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf M)) :=
    Nat.coprime_two_left.mpr (hNodd.of_dvd_nat hdvd)
  exact le_sSup (s := {K : Subgroup ↥M | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hNn, hcop⟩
    (show (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M from hxN)

theorem odd_card_pPrimeCore_map (M : Subgroup G) :
    Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype)) := by
  rw [Subgroup.card_map_of_injective M.subtype_injective]
  exact odd_card_pPrimeCore_two ↥M

omit [Finite G] in
theorem conj_mem_pPrimeCore_map {M : Subgroup G} {r : G} (hr : r ∈ M) {o : G}
    (ho : o ∈ (pPrimeCore 2 ↥M).map M.subtype) : r * o * r⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype :=
  (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M
    (pPrimeCore 2 ↥M) (le_normalizer hr)) o).mp ho

theorem conj_mem_pPrimeCore_map_of_map_eq {M : Subgroup G} {b : G}
    (hMb : M.map (MulAut.conj b).toMonoidHom = M) {o : G}
    (ho : o ∈ (pPrimeCore 2 ↥M).map M.subtype) :
    b * o * b⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  set OM := (pPrimeCore 2 ↥M).map M.subtype with hOM
  set N := OM.map (MulAut.conj b).toMonoidHom with hN
  have hNM : N ≤ M := by
    rw [← hMb]
    exact map_mono (map_subtype_le _)
  have hbo : b * o * b⁻¹ ∈ N := ⟨o, ho, rfl⟩
  have hnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    rintro m hm _ ⟨o', ho', rfl⟩
    have hm' : b⁻¹ * m * b ∈ M := by
      have h1 : m ∈ M.map (MulAut.conj b).toMonoidHom := hMb.symm ▸ hm
      rw [mem_map_equiv, MulAut.conj_symm_apply] at h1
      exact h1
    refine ⟨(b⁻¹ * m * b) * o' * (b⁻¹ * m * b)⁻¹, conj_mem_pPrimeCore_map hm' ho', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective (MulAut.conj b).injective]
    exact odd_card_pPrimeCore_map M
  exact ⟨⟨_, hNM hbo⟩, mem_pPrimeCore_of_normal hnorm hNodd (hNM hbo) hbo, rfl⟩

namespace Step6

variable (d : Step6 z L S)

abbrev M : Subgroup G := centralizer {z} ⊓ centralizer {d.z₁}

abbrev OM : Subgroup G := (pPrimeCore 2 ↥d.M).map d.M.subtype

omit [Finite G] in
theorem map_conj_b (hc : z * d.z₁ = d.z₁ * z) :
    d.M.map (MulAut.conj d.b).toMonoidHom = d.M ∧
      d.J₁.map (MulAut.conj d.b).toMonoidHom = d.J₃ ∧
      d.J₂.map (MulAut.conj d.b).toMonoidHom = d.J₂ ∧
      d.J₃.map (MulAut.conj d.b).toMonoidHom = d.J₁ := by
  have hMb : d.M.map (MulAut.conj d.b).toMonoidHom = d.M := by
    change (centralizer ({z} : Set G) ⊓ centralizer {d.z₁}).map (MulAut.conj d.b).toMonoidHom =
      centralizer {z} ⊓ centralizer {d.z₁}
    rw [Subgroup.map_inf _ _ _ (MulAut.conj d.b).injective, map_centralizer_singleton_mulEquiv,
      map_centralizer_singleton_mulEquiv, MulAut.conj_apply, MulAut.conj_apply, d.hbz, d.hbz₁,
      inf_comm (centralizer {z * d.z₁}) (centralizer {d.z₁}), hc, T23.centralizer_inf_mul,
      inf_comm (centralizer {d.z₁}) (centralizer {z})]
  have key : ∀ {J : Subgroup G}, IsTwoComponentIn J d.M →
      IsTwoComponentIn (J.map (MulAut.conj d.b).toMonoidHom) d.M := fun hJ => by
    have h1 := L35.isTwoComponentIn_map_of_injective (MulAut.conj d.b).toMonoidHom
      (MulAut.conj d.b).injective hJ
    rwa [hMb] at h1
  have hz₁z₁ : d.z₁ * d.z₁ = 1 := by rw [← sq, ← d.hz₁, pow_orderOf_eq_one]
  have hbzz₁ : d.b * (z * d.z₁) * d.b⁻¹ = z := by
    calc d.b * (z * d.z₁) * d.b⁻¹ = (d.b * z * d.b⁻¹) * (d.b * d.z₁ * d.b⁻¹) := by group
      _ = z := by rw [d.hbz, d.hbz₁, mul_assoc, hz₁z₁, mul_one]
  exact ⟨hMb, d.uniq₃ _ (key d.hJ₁) ⟨z, d.hzJ₁, d.hbz⟩,
    d.uniq₂ _ (key d.hJ₂) ⟨d.z₁, d.hz₁J₂, d.hbz₁⟩,
    d.uniq₁ _ (key d.hJ₃) ⟨z * d.z₁, d.hzz₁J₃, hbzz₁⟩⟩

@[expose] def Y : Subgroup G where
  carrier := {r | r ∈ d.M ∧ ∀ j : G, (j ∈ d.J₁ ∨ j ∈ d.J₂ ∨ j ∈ d.J₃) →
    r * j * r⁻¹ * j⁻¹ ∈ d.OM}
  mul_mem' {a c} ha hc := by
    refine ⟨mul_mem ha.1 hc.1, fun j hj => ?_⟩
    have h1 := ha.2 j hj
    have h2 := conj_mem_pPrimeCore_map ha.1 (hc.2 j hj)
    have h3 : a * c * j * (a * c)⁻¹ * j⁻¹ =
        a * (c * j * c⁻¹ * j⁻¹) * a⁻¹ * (a * j * a⁻¹ * j⁻¹) := by group
    rw [h3]
    exact mul_mem h2 h1
  one_mem' := ⟨one_mem _, fun j _ => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, fun j hj => ?_⟩
    have h1 := conj_mem_pPrimeCore_map (inv_mem ha.1) (inv_mem (ha.2 j hj))
    have h3 : a⁻¹ * j * a⁻¹⁻¹ * j⁻¹ = a⁻¹ * (a * j * a⁻¹ * j⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h3]
    exact h1

omit [Finite G] in
theorem mem_Y {r : G} : r ∈ d.Y ↔ r ∈ d.M ∧ ∀ j : G, (j ∈ d.J₁ ∨ j ∈ d.J₂ ∨ j ∈ d.J₃) →
    r * j * r⁻¹ * j⁻¹ ∈ d.OM :=
  Iff.rfl

theorem conj_b_mem_Y (hc : z * d.z₁ = d.z₁ * z) {r : G} (hr : r ∈ d.Y) :
    d.b * r * d.b⁻¹ ∈ d.Y := by
  obtain ⟨hMb, h₁, h₂, h₃⟩ := d.map_conj_b hc
  obtain ⟨hrM, hrJ⟩ := (d.mem_Y).mp hr
  refine (d.mem_Y).mpr ⟨?_, fun j hj => ?_⟩
  · rw [← hMb]
    exact ⟨r, hrM, rfl⟩
  · have hback : ∀ {J J' : Subgroup G}, J'.map (MulAut.conj d.b).toMonoidHom = J → j ∈ J →
        d.b⁻¹ * j * d.b ∈ J' := by
      intro J J' hJJ hjJ
      rw [← hJJ] at hjJ
      obtain ⟨j', hj', rfl⟩ := hjJ
      have h1 : d.b⁻¹ * ((MulAut.conj d.b).toMonoidHom j') * d.b = j' := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h1]
      exact hj'
    have hj' : d.b⁻¹ * j * d.b ∈ d.J₁ ∨ d.b⁻¹ * j * d.b ∈ d.J₂ ∨ d.b⁻¹ * j * d.b ∈ d.J₃ := by
      rcases hj with hj | hj | hj
      · exact .inr (.inr (hback h₃ hj))
      · exact .inr (.inl (hback h₂ hj))
      · exact .inl (hback h₁ hj)
    have h2 := conj_mem_pPrimeCore_map_of_map_eq hMb (hrJ _ hj')
    rw [show d.b * (r * (d.b⁻¹ * j * d.b) * r⁻¹ * (d.b⁻¹ * j * d.b)⁻¹) * d.b⁻¹ =
      d.b * r * d.b⁻¹ * j * (d.b * r * d.b⁻¹)⁻¹ * j⁻¹ by group] at h2
    exact h2

end Step6

theorem commute_of_mem_coreActionKernel {S L : Subgroup G} (hS : IsPGroup 2 S) {s x : G}
    (hsS : s ∈ S) (hsK : s ∈ coreActionKernel L) (hxS : x ∈ S) (hxL : x ∈ L) :
    s * x = x * s := by
  have h1 := (mem_coreActionKernel.mp (inv_mem hsK)).2 x⁻¹ (inv_mem hxL)
  rw [inv_inv, inv_inv] at h1
  have h2 : s * x * s⁻¹ * x⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    have h3 := inv_mem h1
    rwa [show (x * s * x⁻¹ * s⁻¹)⁻¹ = s * x * s⁻¹ * x⁻¹ by group] at h3
  have hcS : s * x * s⁻¹ * x⁻¹ ∈ S :=
    mul_mem (mul_mem (mul_mem hsS hxS) (inv_mem hsS)) (inv_mem hxS)
  obtain ⟨n, hn⟩ := hS ⟨_, hcS⟩
  have hn' : (s * x * s⁻¹ * x⁻¹) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h4 := eq_one_of_two_pow_of_odd (odd_card_pPrimeCore_map L) h2 hn'
  calc s * x = s * x * s⁻¹ * x⁻¹ * (x * s) := by group
    _ = x * s := by rw [h4, one_mul]

namespace Step6

variable (d : Step6 z L S)

section Certified

theorem inf_Q_le_Y (hI : C3Inputs) (h : C3Config G z L p f)
    (hS : IsSylowOf 2 S (centralizer {z})) :
    S ⊓ (centralizer {z} ⊓ coreActionKernel L) ≤ d.Y := by
  intro s hs
  obtain ⟨hsS, hsQ⟩ := mem_inf.mp hs
  obtain ⟨hsz, hsK⟩ := mem_inf.mp hsQ
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  have hON : ∀ x ∈ centralizer ({z} : Set G), ∀ o ∈ (pPrimeCore 2 ↥L).map L.subtype,
      x * o * x⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := fun x hx o ho =>
    (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L
      (pPrimeCore 2 ↥L) (hHN hx)) o).mp ho
  have hsz₁ : s * d.z₁ = d.z₁ * s :=
    commute_of_mem_coreActionKernel hS.isPGroup hsS hsK d.hz₁S d.hz₁L
  have hsM : s ∈ d.M := mem_inf.mpr ⟨hsz, mem_centralizer_singleton_iff.mpr hsz₁⟩
  refine (d.mem_Y).mpr ⟨hsM, fun j hj => ?_⟩
  have hjL : j ∈ L := by
    rcases hj with hj | hj | hj
    exacts [d.hJ₁L hj, d.hJ₂L hj, d.hJ₃L hj]
  have hjM : j ∈ d.M := by
    rcases hj with hj | hj | hj
    exacts [d.hJ₁.1 hj, d.hJ₂.1 hj, d.hJ₃.1 hj]
  have h1 : j⁻¹ * s * j * s⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    have h2 := (mem_coreActionKernel.mp (inv_mem hsK)).2 j hjL
    rwa [inv_inv] at h2
  have h2 : s * j * s⁻¹ * j⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    have h3 := hON j (h.hL.1 hjL) _ h1
    rwa [show j * (j⁻¹ * s * j * s⁻¹) * j⁻¹ = s * j * s⁻¹ * j⁻¹ by group] at h3
  have hM : s * j * s⁻¹ * j⁻¹ ∈ d.M :=
    mul_mem (mul_mem (mul_mem hsM hjM) (inv_mem hsM)) (inv_mem hjM)
  exact ⟨⟨_, hM⟩, mem_pPrimeCore_of_normal (fun m hm o ho => hON m (mem_inf.mp hm).1 o ho)
    (odd_card_pPrimeCore_map L) hM h2, rfl⟩

theorem mem_Q_of_mem_Y (hI : C3Inputs) (h : C3Config G z L p f) {r : G} (hr : r ∈ d.Y) :
    r ∈ coreActionKernel L ∨ r * d.z₁⁻¹ ∈ coreActionKernel L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrM, hrJ⟩ := (d.mem_Y).mp hr
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  have hrN : r ∈ normalizer (L : Set G) := hHN (mem_inf.mp hrM).1
  have hz₁' : orderOf (⟨d.z₁, d.hz₁L⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact d.hz₁
  have hz₁sq : (⟨d.z₁, d.hz₁L⟩ : ↥L) * ⟨d.z₁, d.hz₁L⟩ = 1 := by
    rw [← sq, ← hz₁', pow_orderOf_eq_one]
  set t : Bar L := QuotientGroup.mk ⟨d.z₁, d.hz₁L⟩ with ht
  have ht2 : orderOf t = 2 := orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥L) hz₁'
  obtain ⟨hO1, hU2⟩ := hI.u2 (Bar L) p f h.hp h.hp2 h.h5 h.hcov t ht2 d.hz₁Z
  have hJbar : ∀ {J : Subgroup G}, IsTwoComponentIn J d.M → J ≤ L →
      IsTwoComponentIn ((J.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)))
        (centralizer {t}) := by
    intro J hJ hJL
    have hJL' : IsTwoComponentIn J (L ⊓ centralizer {d.z₁}) :=
      ⟨le_inf hJL (hJ.1.trans inf_le_right),
        L219.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ h.hL.1) hJ.2.1, hJ.2.2⟩
    exact (isTwoComponentIn_map_bar hz₁' (isTwoComponentIn_subgroupOf_inf d.hz₁L hJL')).1
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  obtain ⟨-, h410t⟩ := hI.l410 (Bar L) p f h.hp h.hp2 h.h5 h.hcov _
    (mk_mem_center_of_mem_center hzc) (mk_ne_one_of_orderOf_two hz')
  obtain ⟨hc2, huniq, -⟩ := h410t t ht2 d.hz₁Z
  have hCt : (centralizer ({⟨d.z₁, d.hz₁L⟩} : Set ↥L)).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) =
      centralizer {t} := map_centralizer_eq (odd_card_pPrimeCore_two ↥L) hz₁sq
  have hOML : ∀ {c : G} (hc : c ∈ d.OM) (hcL : c ∈ L), (⟨c, hcL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := by
    intro c hc hcL
    set N : Subgroup (Bar L) :=
      ((d.OM ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) with hN
    have hNC : N ≤ centralizer {t} := by
      rintro _ ⟨⟨o, hoL⟩, ho, rfl⟩
      rw [← hCt]
      refine ⟨⟨o, hoL⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hoM : o ∈ d.M := map_subtype_le _ (mem_inf.mp ho).1
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp hoM).2
    have hnorm : ∀ m ∈ centralizer {t}, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
      intro m hm n hn
      rw [← hCt] at hm
      obtain ⟨y, hy, rfl⟩ := hm
      obtain ⟨⟨o, hoL⟩, ho, rfl⟩ := hn
      have hyM : (y : G) ∈ d.M := mem_inf.mpr ⟨h.hL.1 y.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
      have ho' := mem_inf.mp ho
      refine ⟨y * ⟨o, hoL⟩ * y⁻¹, mem_inf.mpr ⟨conj_mem_pPrimeCore_map hyM ho'.1,
        mul_mem (mul_mem y.2 hoL) (inv_mem y.2)⟩, ?_⟩
      simp only [map_mul, map_inv]
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card ↥((d.OM ⊓ L).subgroupOf L) := Subgroup.card_map_dvd _ _
      have h2 : Nat.card ↥((d.OM ⊓ L).subgroupOf L) ∣ Nat.card ↥d.OM := by
        rw [← Subgroup.card_map_of_injective L.subtype_injective, subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
      exact (odd_card_pPrimeCore_map d.M).of_dvd_nat (h1.trans h2)
    have hcN : (QuotientGroup.mk ⟨c, hcL⟩ : Bar L) ∈ N := ⟨⟨c, hcL⟩, mem_inf.mpr ⟨hc, hcL⟩, rfl⟩
    have h1 := mem_pPrimeCore_of_normal hnorm hNodd (hNC hcN) hcN
    rw [hO1, mem_bot] at h1
    have h2 : (QuotientGroup.mk ⟨c, hcL⟩ : Bar L) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hfix : ∀ J : Subgroup (Bar L), IsTwoComponentIn J (centralizer {t}) →
      ∀ j ∈ J, barAction L ⟨r, hrN⟩ j = j := by
    intro J hJ j hj
    have hJeq : ∃ Ji : Subgroup G, (Ji = d.J₁ ∨ Ji = d.J₂ ∨ Ji = d.J₃) ∧
        J = (Ji.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := by
      rcases (hc2 J hJ).2 with hzJ | htJ | hztJ
      · exact ⟨d.J₁, .inl rfl, huniq J _ hJ (hJbar d.hJ₁ d.hJ₁L) _ (Set.mem_insert _ _) hzJ
          ⟨⟨z, h.hzL⟩, d.hzJ₁, rfl⟩⟩
      · exact ⟨d.J₂, .inr (.inl rfl), huniq J _ hJ (hJbar d.hJ₂ d.hJ₂L) _
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) htJ ⟨⟨d.z₁, d.hz₁L⟩, d.hz₁J₂, rfl⟩⟩
      · exact ⟨d.J₃, .inr (.inr rfl), huniq J _ hJ (hJbar d.hJ₃ d.hJ₃L) _
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hztJ
          ⟨⟨z * d.z₁, mul_mem h.hzL d.hz₁L⟩, d.hzz₁J₃, rfl⟩⟩
    obtain ⟨Ji, hJi, rfl⟩ := hJeq
    obtain ⟨⟨j₀, hj₀L⟩, hj₀J, rfl⟩ := hj
    have hj₀ : j₀ ∈ d.J₁ ∨ j₀ ∈ d.J₂ ∨ j₀ ∈ d.J₃ := by
      rcases hJi with rfl | rfl | rfl
      exacts [.inl hj₀J, .inr (.inl hj₀J), .inr (.inr hj₀J)]
    have hc := hrJ j₀ hj₀
    have hrj : r * j₀ * r⁻¹ ∈ L := (mem_normalizer_iff.mp hrN j₀).mp hj₀L
    have hcL : r * j₀ * r⁻¹ * j₀⁻¹ ∈ L := mul_mem hrj (inv_mem hj₀L)
    have hcO := hOML hc hcL
    rw [QuotientGroup.mk'_apply, barAction_mk, QuotientGroup.eq]
    have h1 : (normalizerConj L ⟨r, hrN⟩ ⟨j₀, hj₀L⟩)⁻¹ * ⟨j₀, hj₀L⟩ =
        (⟨j₀, hj₀L⟩ : ↥L)⁻¹ * (⟨_, hcL⟩ : ↥L)⁻¹ * ((⟨j₀, hj₀L⟩ : ↥L)⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply, inv_inv]
      group
    rw [h1]
    exact (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem _ (inv_mem hcO) _
  rcases hU2 (barAction L ⟨r, hrN⟩) hfix with hα | hα
  · exact .inl ((mem_ker_barAction L ⟨r, hrN⟩).mp (MonoidHom.mem_ker.mpr hα))
  · right
    have hz₁N : d.z₁ ∈ normalizer (L : Set G) := le_normalizer d.hz₁L
    have h1 : barAction L ⟨d.z₁, hz₁N⟩ = MulAut.conj t :=
      barAction_of_mem L ⟨d.z₁, d.hz₁L⟩ hz₁N
    have h2 : barAction L ⟨r * d.z₁⁻¹, mul_mem hrN (inv_mem hz₁N)⟩ = 1 := by
      have h3 : (⟨r * d.z₁⁻¹, mul_mem hrN (inv_mem hz₁N)⟩ : ↥(normalizer (L : Set G))) =
          ⟨r, hrN⟩ * (⟨d.z₁, hz₁N⟩)⁻¹ := rfl
      rw [h3, map_mul, map_inv, hα, h1]
      exact mul_inv_cancel _
    exact (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h2)

end Certified

end Step6

end CFSG.ComponentClassification.HarrisLit.T1

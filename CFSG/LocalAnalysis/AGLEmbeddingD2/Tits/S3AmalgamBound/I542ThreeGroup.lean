module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open scoped commutatorElement

section Basic

variable {Y : Type*} [Group Y] {E L J : Subgroup Y}

theorem commutator_le_of_normal (hL : L.Normal) (J : Subgroup Y) : ⁅L, J⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro l hl j _
  have h1 : j * l⁻¹ * j⁻¹ ∈ L := hL.conj_mem _ (L.inv_mem hl) j
  have e : ⁅l, j⁆ = l * (j * l⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [e]; exact L.mul_mem hl h1

theorem commutator_commutator_eq (hL : L.Normal) [hE : E.Normal]
    (hEJ : ∀ j ∈ J, ∀ e ∈ E, j * e = e * j) (hLJ : L ≤ ⁅L, J⁆ ⊔ E) :
    ⁅⁅L, J⁆, J⁆ = ⁅L, J⁆ := by
  apply le_antisymm
  · exact Subgroup.commutator_mono (commutator_le_of_normal hL J) le_rfl
  · rw [Subgroup.commutator_le]
    intro l hl j hj
    obtain ⟨r, hr, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hLJ hl)
    have e1 : ⁅r * e, j⁆ = ⁅r, j⁆ := by
      have hcomm : j * e = e * j := hEJ j hj e he
      have : (r * e) * j * (r * e)⁻¹ * j⁻¹ = r * j * r⁻¹ * j⁻¹ := by
        have h2 : e * j * e⁻¹ = j := by rw [← hcomm]; group
        calc (r * e) * j * (r * e)⁻¹ * j⁻¹ = r * (e * j * e⁻¹) * r⁻¹ * j⁻¹ := by group
          _ = r * j * r⁻¹ * j⁻¹ := by rw [h2]
      simpa [commutatorElement_def] using this
    rw [e1]
    exact Subgroup.commutator_mem_commutator hr hj


theorem commutator_eq_bot_of_commute {A B : Subgroup Y} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ⁅A, B⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (h a ha b hb)

theorem commutator_bot_left (B : Subgroup Y) : ⁅(⊥ : Subgroup Y), B⁆ = ⊥ :=
  commutator_eq_bot_of_commute fun a ha b _ => by
    rw [Subgroup.mem_bot] at ha; subst ha; simp

theorem comm_mem' {S : Subgroup Y} {a b : Y} (ha : a ∈ S) (hb : b ∈ S) : ⁅a, b⁆ ∈ S := by
  rw [commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem commutator_self_le (H : Subgroup Y) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem inf_commutes (hL : L.Normal) [hE : E.Normal]
    (hEJ : ∀ j ∈ J, ∀ e ∈ E, j * e = e * j) (hLJ : L ≤ ⁅L, J⁆ ⊔ E) :
    ∀ n ∈ ⁅L, J⁆ ⊓ E, ∀ r ∈ ⁅L, J⁆, n * r = r * n := by
  set R := ⁅L, J⁆ with hR
  have hRJ : ⁅R, J⁆ = R := commutator_commutator_eq hL hEJ hLJ
  have hEJ' : ⁅E, J⁆ = ⊥ := commutator_eq_bot_of_commute fun e he j hj => (hEJ j hj e he).symm
  have h1 : ⁅⁅J, R ⊓ E⁆, R⁆ = ⊥ := by
    have : ⁅J, R ⊓ E⁆ = ⊥ :=
      commutator_eq_bot_of_commute fun j hj n hn => hEJ j hj n hn.2
    rw [this]; exact commutator_bot_left R
  have h2 : ⁅⁅R ⊓ E, R⁆, J⁆ = ⊥ := by
    have h3 : ⁅R ⊓ E, R⁆ ≤ E :=
      (Subgroup.commutator_mono inf_le_right le_rfl).trans (Subgroup.commutator_le_left E R)
    rw [eq_bot_iff, ← hEJ']
    exact Subgroup.commutator_mono h3 le_rfl
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := R) (H₂ := J) (H₃ := R ⊓ E) h1 h2
  rw [hRJ] at h3
  intro n hn r hr
  have : ⁅r, n⁆ ∈ ⁅R, R ⊓ E⁆ := Subgroup.commutator_mem_commutator hr hn
  rw [h3, Subgroup.mem_bot] at this
  exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm


theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    refine hnc ⟨⟨fun a b => ?_⟩⟩
    have : b ∈ Subgroup.center S := by rw [h]; trivial
    exact Subgroup.mem_center_iff.mp this a

theorem commutator_eq_self_of_simple {Q : Type*} [Group Q] {S : Subgroup Q} [IsSimpleGroup ↥S]
    (hnc : ¬ IsMulCommutative ↥S) : ⁅S, S⁆ = S := by
  have hle : ⁅S, S⁆ ≤ S := commutator_self_le S
  have hN : (⁅S, S⁆.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    exact le_normalizer_commutator_left S S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅S, S⁆.subgroupOf S) with h | h
  · exfalso
    refine hnc ⟨⟨fun a b => ?_⟩⟩
    have hm : (⟨⁅(a : Q), (b : Q)⁆, comm_mem' a.2 b.2⟩ : ↥S) ∈ ⁅S, S⁆.subgroupOf S :=
      Subgroup.commutator_mem_commutator a.2 b.2
    rw [h, Subgroup.mem_bot] at hm
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hm))
  · refine le_antisymm hle fun s hs => ?_
    have : (⟨s, hs⟩ : ↥S) ∈ ⁅S, S⁆.subgroupOf S := by rw [h]; trivial
    exact this


theorem commutator_mul_of_commute {p e j : Y} (hcomm : j * e = e * j) :
    ⁅p * e, j⁆ = ⁅p, j⁆ := by
  have h2 : e * j * e⁻¹ = j := by rw [← hcomm]; group
  simp only [commutatorElement_def]
  calc p * e * j * (p * e)⁻¹ * j⁻¹ = p * (e * j * e⁻¹) * p⁻¹ * j⁻¹ := by group
    _ = p * j * p⁻¹ * j⁻¹ := by rw [h2]

theorem commutator_central_right {r z x : Y} (h : z * x = x * z) : ⁅r * z, x⁆ = ⁅r, x⁆ := by
  have h2 : z * x * z⁻¹ = x := by rw [h]; group
  simp only [commutatorElement_def]
  calc r * z * x * (r * z)⁻¹ * x⁻¹ = r * (z * x * z⁻¹) * r⁻¹ * x⁻¹ := by group
    _ = r * x * r⁻¹ * x⁻¹ := by rw [h2]

theorem commutator_central_left {r z x : Y} (h : z * x = x * z) : ⁅x, r * z⁆ = ⁅x, r⁆ := by
  have h2 : z * x⁻¹ * z⁻¹ = x⁻¹ := by
    have : z * x⁻¹ = x⁻¹ * z := by
      have h' : x * z = z * x := h.symm
      calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
        _ = x⁻¹ * (z * x) * x⁻¹ := by rw [h']
        _ = x⁻¹ * z := by group
    rw [this]; group
  simp only [commutatorElement_def]
  calc x * (r * z) * x⁻¹ * (r * z)⁻¹ = x * r * (z * x⁻¹ * z⁻¹) * r⁻¹ := by group
    _ = x * r * x⁻¹ * r⁻¹ := by rw [h2]

theorem le_normalizer_commutator_right (L J : Subgroup Y) :
    J ≤ Subgroup.normalizer ((⁅L, J⁆ : Subgroup Y) : Set Y) := by
  rw [Subgroup.commutator_comm L J]
  exact le_normalizer_commutator_left J L

theorem commutator_self_eq (hL : L.Normal) [hE : E.Normal]
    (hEJ : ∀ j ∈ J, ∀ e ∈ E, j * e = e * j) (hLJ : L ≤ ⁅L, J⁆ ⊔ E)
    {Q : Type*} [Group Q] (f : Y →* Q) (hf : f.ker = E)
    (hS : IsSimpleGroup ↥(L.map f))
    (hnc : ¬ IsMulCommutative ↥(L.map f)) :
    ⁅⁅L, J⁆, ⁅L, J⁆⁆ = ⁅L, J⁆ := by
  set R := ⁅L, J⁆ with hR
  have hRL : R ≤ L := commutator_le_of_normal hL J
  have hRJ : ⁅R, J⁆ = R := commutator_commutator_eq hL hEJ hLJ
  have hSeq : L.map f = R.map f := by
    apply le_antisymm
    · calc L.map f ≤ (R ⊔ E).map f := Subgroup.map_mono hLJ
        _ = R.map f := by rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff E).mpr hf.ge, sup_bot_eq]
    · exact Subgroup.map_mono hRL
  have hcs : ⁅L.map f, L.map f⁆ = L.map f := commutator_eq_self_of_simple hnc
  have hRpS : (⁅R, R⁆).map f = L.map f := by
    rw [Subgroup.map_commutator, ← hSeq]; exact hcs
  have hLRp : L ≤ ⁅R, R⁆ ⊔ E := by
    intro l hl
    have h1 : f l ∈ L.map f := Subgroup.mem_map_of_mem f hl
    rw [← hRpS] at h1
    obtain ⟨p, hp, hpl⟩ := h1
    have h2 : p⁻¹ * l ∈ E := by
      rw [← hf, MonoidHom.mem_ker, map_mul, map_inv, hpl, inv_mul_cancel]
    have : l = p * (p⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hp h2
  have hjN : ∀ j ∈ J, j ∈ Subgroup.normalizer (R : Set Y) := fun j hj =>
    le_normalizer_commutator_right L J hj
  have hjRp : ∀ j ∈ J, j ∈ Subgroup.normalizer ((⁅R, R⁆ : Subgroup Y) : Set Y) := fun j hj =>
    mem_normalizer_commutator (hjN j hj) (hjN j hj)
  apply le_antisymm (commutator_self_le R)
  calc R = ⁅R, J⁆ := hRJ.symm
    _ ≤ ⁅R, R⁆ := by
      rw [Subgroup.commutator_le]
      intro r hr j hj
      obtain ⟨p, hp, e, he, hpe⟩ := Subgroup.mem_sup_of_normal_right.mp (hLRp (hRL hr))
      subst hpe
      rw [commutator_mul_of_commute (hEJ j hj e he)]
      rw [commutatorElement_def]
      have h1 : j * p⁻¹ * j⁻¹ ∈ ⁅R, R⁆ :=
        (Subgroup.mem_normalizer_iff.mp (hjRp j hj) p⁻¹).mp ((⁅R, R⁆).inv_mem hp)
      have e1 : p * j * p⁻¹ * j⁻¹ = p * (j * p⁻¹ * j⁻¹) := by group
      rw [e1]
      exact (⁅R, R⁆).mul_mem hp h1

theorem commutator_commutator_E (hL : L.Normal) [hE : E.Normal] (hEL : E ≤ L)
    (hEJ : ∀ j ∈ J, ∀ e ∈ E, j * e = e * j) (hLJ : L ≤ ⁅L, J⁆ ⊔ E)
    {Q : Type*} [Group Q] (f : Y →* Q) (hf : f.ker = E)
    (hS : IsSimpleGroup ↥(L.map f))
    (hnc : ¬ IsMulCommutative ↥(L.map f)) :
    ⁅⁅L, J⁆, E⁆ = ⊥ := by
  set R := ⁅L, J⁆ with hR
  have hperf := commutator_self_eq hL hEJ hLJ f hf hS hnc
  have hcomm := inf_commutes hL hEJ hLJ
  have hRE : ⁅R, E⁆ ≤ R ⊓ E := by
    refine le_inf ?_ (Subgroup.commutator_le_right R E)
    rw [Subgroup.commutator_le]
    intro r hr e he
    have h1 : e * r⁻¹ * e⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator_left L J (hEL he)) r⁻¹).mp
        (R.inv_mem hr)
    have e1 : ⁅r, e⁆ = r * (e * r⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e1]; exact R.mul_mem hr h1
  have h1 : ⁅⁅R, E⁆, R⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono hRE le_rfl).trans ?_
    rw [commutator_eq_bot_of_commute (A := R ⊓ E) (B := R) fun n hn r hr => hcomm n hn r hr]
  have h2 : ⁅⁅E, R⁆, R⁆ = ⊥ := by rw [Subgroup.commutator_comm E R]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := R) (H₂ := R) (H₃ := E) h1 h2
  rwa [hperf] at h3


theorem normal_commutator_commutator (hL : L.Normal) [hE : E.Normal] (hEL : E ≤ L)
    (hEJ : ∀ j ∈ J, ∀ e ∈ E, j * e = e * j) (hLJ : L ≤ ⁅L, J⁆ ⊔ E)
    {Q : Type*} [Group Q] (f : Y →* Q) (hf : f.ker = E)
    (hS : IsSimpleGroup ↥(L.map f))
    (hnc : ¬ IsMulCommutative ↥(L.map f)) :
    (⁅L, J⁆).Normal := by
  set R := ⁅L, J⁆ with hR
  have hperf := commutator_self_eq hL hEJ hLJ f hf hS hnc
  have hRE := commutator_commutator_E hL hEL hEJ hLJ f hf hS hnc
  have hRL : R ≤ L := commutator_le_of_normal hL J
  have hRc : ∀ r ∈ R, ∀ e ∈ E, r * e = e * r := fun r hr e he => by
    have : ⁅r, e⁆ ∈ ⁅R, E⁆ := Subgroup.commutator_mem_commutator hr he
    rw [hRE, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  set D0 : Subgroup Y := L ⊓ Subgroup.centralizer (E : Set Y) with hD0
  haveI hD0n : D0.Normal := by
    refine ⟨fun d hd y => ⟨hL.conj_mem d hd.1 y, ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro e he
    have he' : y⁻¹ * e * y⁻¹⁻¹ ∈ E := hE.conj_mem e he y⁻¹
    have hdc := Subgroup.mem_centralizer_iff.mp hd.2 _ he'
    calc e * (y * d * y⁻¹) = y * ((y⁻¹ * e * y⁻¹⁻¹) * d) * y⁻¹ := by group
      _ = y * (d * (y⁻¹ * e * y⁻¹⁻¹)) * y⁻¹ := by rw [hdc]
      _ = y * d * y⁻¹ * e := by group
  have hRD0 : R ≤ D0 := le_inf hRL (fun r hr =>
    Subgroup.mem_centralizer_iff.mpr (fun e he => (hRc r hr e he).symm))
  have hD0R : ⁅D0, D0⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro d hd d' hd'
    obtain ⟨r, hr, e, he, hre⟩ := Subgroup.mem_sup_of_normal_right.mp (hLJ hd.1)
    obtain ⟨r', hr', e', he', hre'⟩ := Subgroup.mem_sup_of_normal_right.mp (hLJ hd'.1)
    subst hre; subst hre'
    have heD : e ∈ D0 := by
      have : r⁻¹ * (r * e) ∈ D0 := D0.mul_mem (D0.inv_mem (hRD0 hr)) hd
      simpa using this
    have he'D : e' ∈ D0 := by
      have : r'⁻¹ * (r' * e') ∈ D0 := D0.mul_mem (D0.inv_mem (hRD0 hr')) hd'
      simpa using this
    have hcen : ∀ z ∈ D0, z ∈ E → ∀ x ∈ D0, z * x = x * z := fun z _ hzE x hx =>
      Subgroup.mem_centralizer_iff.mp hx.2 z hzE
    have h1 : ⁅r * e, r' * e'⁆ = ⁅r, r' * e'⁆ :=
      commutator_central_right (hcen e heD he _ hd')
    have h2 : ⁅r, r' * e'⁆ = ⁅r, r'⁆ :=
      commutator_central_left (hcen e' he'D he' r (hRD0 hr))
    rw [h1, h2]
    exact Subgroup.commutator_mem_commutator hr hr' |> fun h => (commutator_self_le R) h
  have : ⁅D0, D0⁆ = R := by
    apply le_antisymm hD0R
    calc R = ⁅R, R⁆ := hperf.symm
      _ ≤ ⁅D0, D0⁆ := Subgroup.commutator_mono hRD0 hRD0
  rw [← this]
  exact Subgroup.commutator_normal D0 D0

theorem mem_of_central (hL : L.Normal) [hE : E.Normal]
    (hLJ : L ≤ ⁅L, J⁆ ⊔ E)
    {Q : Type*} [Group Q] (f : Y →* Q) (hf : f.ker = E)
    (hS : IsSimpleGroup ↥(L.map f))
    (hnc : ¬ IsMulCommutative ↥(L.map f)) {z : Y}
    (hz : z ∈ ⁅L, J⁆) (hzc : ∀ r ∈ ⁅L, J⁆, z * r = r * z) : z ∈ E := by
  set R := ⁅L, J⁆ with hR
  have hRL : R ≤ L := commutator_le_of_normal hL J
  have hSeq : L.map f = R.map f := by
    apply le_antisymm
    · calc L.map f ≤ (R ⊔ E).map f := Subgroup.map_mono hLJ
        _ = R.map f := by rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff E).mpr hf.ge, sup_bot_eq]
    · exact Subgroup.map_mono hRL
  have hzS : f z ∈ L.map f := Subgroup.mem_map.mpr ⟨z, hRL hz, rfl⟩
  have hcen : (⟨f z, hzS⟩ : ↥(L.map f)) ∈ Subgroup.center ↥(L.map f) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨s, hs⟩
    rw [hSeq] at hs
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hs
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hzc r hr]
  rw [center_eq_bot_of_simple hnc, Subgroup.mem_bot] at hcen
  have : f z = 1 := congrArg Subtype.val hcen
  rw [← hf]; exact this

end Basic

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

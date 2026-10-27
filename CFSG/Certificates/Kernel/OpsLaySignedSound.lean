module

public import Certificates.Data.Kernel.OpsLaySigned
public import CFSG.Certificates.Kernel.OpsV4Sound

public section

namespace CFSG.KC.OpsLaySigned

open CFSG.SectionRank.Native CFSG.SectionRank.QTK.CoverB CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native CFSG.KC.LQT CFSG.KC.OpsLayK
  CFSG.KC.OpsV4

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

variable {M V₀ V : Type} {O₀ : Ops M V₀} {O : Ops Nat V}

theorem v4conjOK_of (S : Sim O₀ O) {X T T₁ T₂ : M} {x t t₁ t₂ : Nat} (hX : S.R X x)
    (hT : S.R T t) (h₁ : S.R T₁ t₁) (h₂ : S.R T₂ t₂) (h : V4Data.conjOK O x t t₁ t₂ = true) :
    V4Data.conjOK O₀ X T T₁ T₂ = true := by
  unfold V4Data.conjOK at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (S.eq (S.mul hX hT) (S.mul h₁ hX) h))
  · exact Or.inl (Or.inr (S.eq (S.mul hX hT) (S.mul h₂ hX) h))
  · exact Or.inr (S.eq (S.mul hX hT) (S.mul (S.mul h₁ h₂) hX) h)

theorem signedCheck_of_G [Inhabited M] (S : Sim O₀ O) {D : SignedData}
    (hp : D.base.prog.all (Op.lt D.base.nregs) = true) {g : Nat → Nat}
    (hg : ∀ r < D.base.nregs, S.R (O₀.run D.base.prog
      (O₀.initRegs (O₀.decode D.base.seedA) (O₀.decode D.base.seedB) D.base.nregs))[r]! (g r))
    (hT : ∀ k ∈ D.base.tests, S.T k) (h : signedG O D g = true) :
    SignedData.check O₀ D = true := by
  unfold signedG at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hr, hel, ht₁, ht₂, hc, hmov, c₁, c₂, c₃, c₄, hd₁, hd₂, hda, hdb, hdb₂⟩ := h
  have hlt : ∀ r ∈ [D.t₁, D.t₂, D.a, D.b, D.d₁, D.d₂], r < D.base.nregs :=
    fun r hr' => of_decide_eq_true (List.all_eq_true.1 hr r hr')
  have r₁ := hg _ (hlt D.t₁ (by simp))
  have r₂ := hg _ (hlt D.t₂ (by simp))
  have ra := hg _ (hlt D.a (by simp))
  have rb := hg _ (hlt D.b (by simp))
  have e₁ := hg _ (hlt D.d₁ (by simp))
  have e₂ := hg _ (hlt D.d₂ (by simp))
  unfold SignedData.check
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨hp, hr, S.elemOK (.cons ra (.cons rb .nil)) hT hel, S.eq (S.mul r₁ r₁) S.one ht₁,
    S.eq (S.mul r₂ r₂) S.one ht₂, S.eq (S.mul r₁ r₂) (S.mul r₂ r₁) hc, ?_,
    v4conjOK_of S ra r₁ r₁ r₂ c₁, v4conjOK_of S ra r₂ r₁ r₂ c₂, v4conjOK_of S rb r₁ r₁ r₂ c₃,
    v4conjOK_of S rb r₂ r₁ r₂ c₄, S.eq (S.mul e₁ e₁) S.one hd₁, S.eq (S.mul e₂ e₂) S.one hd₂,
    S.eq (S.mul e₁ ra) (S.mul (S.mul ra ra) e₁) hda, S.eq (S.mul e₁ rb) (S.mul rb e₁) hdb,
    S.eq (S.mul e₂ rb) (S.mul (S.mul rb rb) e₂) hdb₂⟩
  obtain ⟨k, hk, hv⟩ := List.any_eq_true.1 hmov
  exact List.any_eq_true.2 ⟨k, hk, S.vne (S.vmul (S.unit (hT k hk)) r₁) (S.unit (hT k hk)) hv⟩

theorem e8Check_of_G [Inhabited M] [Inhabited V₀] (S : Sim O₀ O) {D : E8Data}
    (hn : 2 ≤ D.nregs) (hp : D.prog.all (Op.lt D.nregs) = true) (hx : D.rx < D.nregs)
    (hh : D.rh < D.nregs) (ho : 0 < D.oh) (hE₂ : S.E 2) (hE : S.E D.oh) (hE' : S.E (D.oh - 1))
    {g : Nat → Nat}
    (hg : ∀ r < D.nregs, S.R (O₀.run D.prog
      (O₀.initRegs (O₀.decode D.seedA) (O₀.decode D.seedB) D.nregs))[r]! (g r))
    (hT : S.T D.t) (h : e8G O S.pw D g = true) : e8Check O₀ D = true := by
  unfold e8G at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hX2, hHo, hv, hc₂, hc₃, hcj⟩ := h
  have rX := hg _ hx
  have rH := hg _ hh
  have rH' := S.pow rH hE'
  have rX₂ := S.mul (S.mul rH rX) rH'
  have rX₃ := S.mul (S.mul rH rX₂) rH'
  unfold e8Check Ops.regsOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨hn, hp, hx, hh, ho, S.eq (S.pow rX hE₂) S.one hX2, S.eq (S.pow rH hE) S.one hHo,
    S.vne (S.vmul (S.unit hT) rX) (S.unit hT) hv, S.eq (S.mul rX rX₂) (S.mul rX₂ rX) hc₂,
    S.eq (S.mul rX rX₃) (S.mul rX₃ rX) hc₃, S.eq (S.mul rH rX₃) (S.mul (S.mul rX rX₂) rH) hcj⟩

theorem signedK_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : SignedData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : signedK c A B D = true) : SignedData.check (ops3 d) D = true := by
  subst hd
  unfold signedK at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hprog, htests⟩, hrun⟩ := h
  have hlt := (Snd.progOK_spec hprog).2
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  exact signedCheck_of_G (Sim.ofL3 c hc hp) hlt (fun r hr => hL.2 r (by rw [hlen]; exact hr))
    (fun k hk => Snd.lt_of_all htests hk) hrun

theorem e8K3_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : E8Data}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : e8K3 c A B D = true) : e8Check (ops3 d) D = true := by
  subst hd
  unfold e8K3 at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hprog, hx⟩, hh⟩, ho⟩, ho'⟩, ht⟩, hrun⟩ := h
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  exact e8Check_of_G (Sim.ofL3 c hc hp) hn hlt hx hh ho (by norm_num : (2 : Nat) < 65536) ho'
    (by omega : D.oh - 1 < 65536)
    (fun r hr => hL.2 r (by rw [hlen]; exact hr)) ht hrun

end CFSG.KC.OpsLaySigned

end
